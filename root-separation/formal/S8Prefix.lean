import S8PlacementSampling

namespace S8.Prefix

open scoped BigOperators
open ProductVariance

section Means
variable {P A : Type*} [Fintype P] [Fintype A] [Nonempty A] [DecidableEq P]

def complete (free : List P) (fixed tape : P → A) : P → A :=
  fun p => if p ∈ free then tape p else fixed p

def conditional (f : (P → A) → ℚ) (free : List P) (fixed : P → A) : ℚ :=
  uniformMean (fun tape => f (complete free fixed tape))

theorem mean_equiv {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y) (f : Y → ℚ) :
    uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean uniformWeight
  simp only [Function.comp_apply]
  rw [Fintype.card_congr e, e.sum_comp f]

theorem mean_product {X Y : Type*} [Fintype X] [Fintype Y] (f : X → Y → ℚ) :
    uniformMean (fun p : X × Y => f p.1 p.2) =
      uniformMean (fun x => uniformMean (f x)) := by
  simp only [uniformMean, uniformWeight, Fintype.card_prod, Nat.cast_mul,
    mul_inv_rev, Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

/-- Conditioning on the next independent primitive splits the current
    conditional expectation into the uniform average over candidate symbols. -/
theorem conditional_cons (f : (P → A) → ℚ) (p : P) (free : List P) (fixed : P → A)
    (hp : p ∉ free) :
    conditional f (p :: free) fixed =
      uniformMean (fun a => conditional f free (Function.update fixed p a)) := by
  classical
  let e := Equiv.funSplitAt p A
  have same (a : A) (ω : P → A) :
      complete (p :: free) fixed (e.symm (a,(e ω).2)) =
        complete free (Function.update fixed p a) ω := by
    funext j
    by_cases h : j = p
    · subst j
      simp [complete, hp, e]
    · simp [complete, e, h]
  let F (a : A) (w : {j : P // j ≠ p} → A) :=
    f (complete (p :: free) fixed (e.symm (a,w)))
  have hrewrite : (fun ω => f (complete (p :: free) fixed ω)) =
      (fun z : A × ({j : P // j ≠ p} → A) => F z.1 z.2) ∘ e := by
    funext ω
    simp [F]
  unfold conditional
  rw [hrewrite, mean_equiv, mean_product]
  congr 1
  funext a
  have h := mean_restrict_primitive (A := A) (Function.Embedding.subtype (fun j : P => j ≠ p))
    (F a)
  exact h.symm.trans (congrArg uniformMean (funext fun ω => congrArg f (same a ω)))

theorem conditional_nil (f : (P → A) → ℚ) (fixed : P → A) :
    conditional f [] fixed = f fixed := by
  change uniformMean (fun _ : P → A => f fixed) = _
  simp only [uniformMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uniformWeight]
  have hp : (Fintype.card (P → A) : ℚ) ≠ 0 := by positivity
  field_simp

end Means

section Greedy
variable {P A B : Type*} [DecidableEq P] [LinearOrder B]

def best (cost : A → B) : List A → A → A
  | [], a => a
  | b :: bs, a => best cost bs (if cost b < cost a then b else a)

theorem best_le_initial (cost : A → B) (values : List A) (a : A) :
    cost (best cost values a) ≤ cost a := by
  induction values generalizing a with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (ih _).trans (by split_ifs with hb; exacts [hb.le,le_rfl])

theorem best_le_member (cost : A → B) (values : List A) (a b : A) (hb : b ∈ values) :
    cost (best cost values a) ≤ cost b := by
  induction values generalizing a with
  | nil => simp at hb
  | cons v vs ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (best_le_initial cost vs _).trans (by split_ifs with h; exacts [le_rfl,le_of_not_gt h])
    · exact ih _ hb

def choose (cost : List P → (P → A) → B) (values : List A) (fallback : A)
    (p : P) (free : List P) (fixed : P → A) : P → A :=
  let w := best (fun a => cost free (Function.update fixed p a)) values fallback
  Function.update fixed p w

def solve (cost : List P → (P → A) → B) (values : List A) (fallback : A) :
    List P → (P → A) → (P → A)
  | [], fixed => fixed
  | p :: free, fixed => solve cost values fallback free (choose cost values fallback p free fixed)

variable [Fintype P] [Fintype A] [Nonempty A]

/-- The implemented choice uses an arbitrary exact order-preserving cost
    evaluator. The reference conditional expectation is only in the proof. -/
theorem solve_le_conditional (f : (P → A) → ℚ)
    (cost : List P → (P → A) → B)
    (order : ∀ free x y, cost free x ≤ cost free y →
      conditional f free x ≤ conditional f free y)
    (values : List A) (covers : ∀ a, a ∈ values) (fallback : A) (free : List P)
    (nodup : free.Nodup) (fixed : P → A) :
    f (solve cost values fallback free fixed) ≤ conditional f free fixed := by
  induction free generalizing fixed with
  | nil => rw [solve, conditional_nil]
  | cons p ps ih =>
    obtain ⟨hp,hn⟩ := List.nodup_cons.1 nodup
    let new := choose cost values fallback p ps fixed
    have hlocal (a : A) : conditional f ps new ≤ conditional f ps (Function.update fixed p a) :=
      order _ _ _ (best_le_member (fun a => cost ps (Function.update fixed p a)) values fallback a (covers a))
    have havg : conditional f ps new ≤ uniformMean (fun a =>
        conditional f ps (Function.update fixed p a)) := by
      have hp : (0 : ℚ) < Fintype.card A := by positivity
      have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hlocal a)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
      unfold uniformMean uniformWeight
      rw [← div_eq_inv_mul]
      apply (le_div_iff₀ hp).2
      exact (mul_comm _ _).le.trans h
    exact (ih hn new).trans (havg.trans_eq (conditional_cons _ _ _ _ hp).symm)

end Greedy

#print axioms conditional_cons
#print axioms best_le_member
#print axioms solve_le_conditional

end S8.Prefix
