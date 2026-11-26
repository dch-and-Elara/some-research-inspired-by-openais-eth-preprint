
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace LayerRecovery
open scoped BigOperators Polynomial
open Polynomial

/-- The Boolean predicate implemented by the guard clauses of J6. -/
def guard {V : Type*} [DecidableEq (V → Bool)]
    (F : (V → Bool) → Bool) (z : Bool) (x : V → Bool) : Bool :=
  if z then F x else decide (x = fun _ => false)

theorem guarded_count {V : Type*} [Fintype V] [DecidableEq V]
    (F : (V → Bool) → Bool) :
    (∑ z : Bool, ∑ x : V → Bool, if guard F z x = true then (1 : ℕ) else 0)
      = 1 + ∑ x : V → Bool, if F x = true then (1 : ℕ) else 0 := by
  classical
  rw [Fintype.sum_bool]
  simp [guard, Nat.add_comm]

/-- In the centered range, an integer residue has at most one lift. -/
theorem centered_lift_unique {m a b : ℤ} (hm : 0 < m)
    (ha : 2 * |a| < m) (hb : 2 * |b| < m)
    (hres : m ∣ a - b) : a = b := by
  obtain ⟨k, hk⟩ := hres
  have hdiff : |a - b| < m := by
    have h := abs_sub_le a 0 b
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  rw [hk, abs_mul, abs_of_pos hm] at hdiff
  by_contra hn
  have hkn : k ≠ 0 := by
    intro he
    apply hn
    rw [he, mul_zero] at hk
    exact sub_eq_zero.mp hk
  have hl : (1 : ℤ) ≤ |k| := by
    have h := abs_pos.mpr hkn
    omega
  nlinarith

theorem odd_factor_recovery (e : ℕ) (he : Odd e) (C a b : ℚ)
    (hn : C ≠ 0) (h : C * a ^ e = C * b ^ e) : a = b :=
  (he.strictMono_pow (R := ℚ)).injective (mul_left_cancel₀ hn h)

/-- J6 algebraic identification, after lifting the oracle residues and
    identifying the public nonzero layer factors. -/
theorem recover_from_odd_layer_samples (p q : ℚ[X]) (s : Finset ℚ)
    (hp : p.natDegree < s.card) (hq : q.natDegree < s.card)
    (layer : ℚ → ℕ) (factor : ℚ → ℚ)
    (hOdd : ∀ x ∈ s, Odd (layer x))
    (hFactor : ∀ x ∈ s, factor x ≠ 0)
    (hSamples : ∀ x ∈ s,
      factor x * (p.eval x) ^ layer x = factor x * (q.eval x) ^ layer x) :
    p = q := by
  classical
  by_contra hn
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hn
  have hsub : s ⊆ (p - q).roots.toFinset := by
    intro x hx
    have he := odd_factor_recovery (layer x) (hOdd x hx) (factor x)
      (p.eval x) (q.eval x) (hFactor x hx) (hSamples x hx)
    simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
      Polynomial.eval_sub, sub_eq_zero] using he
  have hl := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  have hd := Polynomial.natDegree_sub_le p q
  have hb := Polynomial.card_roots' (p - q)
  omega

/-- Exact magnitude of the normalized root Lagrange scalar at positive t. -/
def gridRatio (L t : ℕ) : ℚ :=
  ∏ j ∈ Finset.range t, ((L : ℚ) + (j+1)) / ((L : ℚ) - (j+1))

theorem gridRatio_pos {L t : ℕ} (ht : t < L) : 0 < gridRatio L t := by
  unfold gridRatio
  apply Finset.prod_pos
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hlt : ((j : ℚ) + 1) < L := by exact_mod_cast (show j+1 < L by omega)
  exact div_pos (by positivity) (sub_pos.mpr hlt)

theorem gridRatio_step {L t : ℕ} (ht : t+1 < L) :
    gridRatio L t < gridRatio L (t+1) := by
  have hp : 0 < gridRatio L t := gridRatio_pos (by omega)
  have hL : 0 < (L : ℚ) - (t+1) := by
    exact sub_pos.mpr (by exact_mod_cast ht)
  have hi : (1 : ℚ) < ((L : ℚ)+(t+1)) / ((L : ℚ)-(t+1)) := by
    apply (lt_div_iff₀ hL).mpr
    have ht₀ : (0 : ℚ) ≤ t := by positivity
    linarith
  calc
    gridRatio L t = gridRatio L t * 1 := (mul_one _).symm
    _ < gridRatio L t * (((L : ℚ)+(t+1))/((L : ℚ)-(t+1))) := mul_lt_mul_of_pos_left hi hp
    _ = gridRatio L (t+1) := by
      unfold gridRatio
      rw [Finset.prod_range_succ]

theorem gridRatio_strict {L x y : ℕ} (hxy : x < y) (hy : y < L) :
    gridRatio L x < gridRatio L y := by
  induction y with
  | zero => omega
  | succ y ih =>
    by_cases he : x = y
    · subst x
      exact gridRatio_step hy
    · exact (ih (by omega) (by omega)).trans (gridRatio_step hy)

theorem negative_mesh_injective (L : ℕ) :
    Set.InjOn (fun t => -(gridRatio L t)) {t : ℕ | t < L} := by
  intro a ha b hb he
  obtain hab | rfl | hba := lt_trichotomy a b
  · exact (ne_of_lt (gridRatio_strict hab hb)) (neg_injective he) |>.elim
  · rfl
  · exact (ne_of_lt (gridRatio_strict hba ha)) (neg_injective he).symm |>.elim

#print axioms gridRatio_step
#print axioms negative_mesh_injective

section LayerPolynomial
variable {Port : Type*} [Fintype Port] [DecidableEq Port]

noncomputable def wireFactor (y x : Bool) : ℚ[X] :=
  if y then (if x then X else 0) else (1 - if x then X else 0)

theorem wireFactor_degree (y x : Bool) : (wireFactor y x).natDegree ≤ 1 := by
  cases y <;> cases x <;> simp [wireFactor]
  exact (Polynomial.natDegree_sub_le _ _).trans (by simp)

theorem wireFactor_eval_one (y x : Bool) :
    (wireFactor y x).eval 1 = if y = x then 1 else 0 := by
  cases y <;> cases x <;> norm_num [wireFactor]

/-- This is the actual finite two-assignment sum in J6, after reindexing
    all planted wire types to one common finite port type. -/
noncomputable def layerPolynomial (A B : (Port → Bool) → ℚ) : ℚ[X] :=
    ∑ y : Port → Bool, ∑ x : Port → Bool,
      C (A y * B x) * ∏ i : Port, wireFactor (y i) (x i)

theorem layerPolynomial_degree (A B : (Port → Bool) → ℚ) :
    (layerPolynomial A B).natDegree ≤ Fintype.card Port := by
  unfold layerPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  apply (Polynomial.natDegree_mul_le).trans
  simp only [Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset Port))
      (fun i _ => wireFactor_degree (y i) (x i)) :
      (∑ i : Port, (wireFactor (y i) (x i)).natDegree) ≤ ∑ _i : Port, 1)

theorem layerPolynomial_eval_one (A B : (Port → Bool) → ℚ) :
    (layerPolynomial A B).eval 1 = ∑ x : Port → Bool, A x * B x := by
  classical
  have hprod (y x : Port → Bool) :
      (∏ i : Port, (if y i = x i then (1 : ℚ) else 0)) = if x = y then 1 else 0 := by
    by_cases h : x = y
    · subst x; simp
    · have hx : ∃ i, y i ≠ x i := by
        by_contra hh
        push_neg at hh
        exact h ((funext hh).symm)
      obtain ⟨i,hi⟩ := hx
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp [layerPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_prod, wireFactor_eval_one, hprod, mul_ite]

/-- The scalar obtained when summing an independent padding equality bit
    with n matched negative unary rows. -/
theorem padding_column_factor (c : ℚ) (n : ℕ) :
    (∑ b : Bool, (if b then 1-c else 1)^n) = 1 + (1-c)^n := by
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem layerPolynomial_eval (A B : (Port → Bool) → ℚ) (c : ℚ) :
    (layerPolynomial A B).eval c =
      ∑ y : Port → Bool, ∑ x : Port → Bool, A y * B x *
        ∏ i : Port, (if y i then (if x i then c else 0) else 1 - if x i then c else 0) := by
  have hf (y x : Bool) : (wireFactor y x).eval c =
      if y then (if x then c else 0) else 1 - if x then c else 0 := by
    cases y <;> cases x <;> simp [wireFactor]
  simp [layerPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_prod, hf]

/-- J6 finite layer identity once the port arrangement is split into its
    independent layers. M indexes each matched pair of layers; C is the set
    of unmatched column layers; P is the set of padding equality columns.
    Unmatched row layers have already been evaluated at zero to obtain one. -/
theorem planted_layer_factorization {M CLayer P : Type*}
    [Fintype M] [Fintype CLayer] [Fintype P]
    [DecidableEq M] [DecidableEq CLayer] [DecidableEq P] (q : ℕ)
    (A B : (Port → Bool) → ℚ) (c : ℚ) (n : P → ℕ) :
    (∑ y : M → (Port → Bool) × (Port → Bool),
     ∑ _x : CLayer → (Fin q → Bool), ∑ b : P → Bool,
      (∏ h : M, A (y h).1 * B (y h).2 *
        ∏ i : Port,
          (if (y h).1 i then (if (y h).2 i then c else 0)
            else 1 - if (y h).2 i then c else 0)) *
        ∏ j : P, (if b j then 1-c else 1) ^ n j) =
      (2 : ℚ) ^ (q * Fintype.card CLayer) *
        (layerPolynomial A B).eval c ^ Fintype.card M *
          ∏ j : P, (1 + (1-c) ^ n j) := by
  classical
  have hp : (∑ b : P → Bool, ∏ j : P, (if b j then 1-c else 1) ^ n j) =
      ∏ j : P, (1 + (1-c) ^ n j) := by
    rw [← Fintype.prod_sum (fun (j : P) (x : Bool) => (if x then 1-c else 1) ^ n j)]
    exact Finset.prod_congr rfl (fun j _ => padding_column_factor c (n j))
  have hc : (∑ _x : CLayer → (Fin q → Bool), (1 : ℚ)) = 2 ^ (q * Fintype.card CLayer) := by
    simp [← pow_mul]
  have hm : (∑ y : M → (Port → Bool) × (Port → Bool),
      ∏ h : M, A (y h).1 * B (y h).2 *
        ∏ i : Port,
          (if (y h).1 i then (if (y h).2 i then c else 0)
            else 1 - if (y h).2 i then c else 0)) =
      (layerPolynomial A B).eval c ^ Fintype.card M := by
    rw [← Fintype.prod_sum (fun (_h : M) (x : (Port → Bool) × (Port → Bool)) =>
      A x.1 * B x.2 * ∏ i : Port, if x.1 i then (if x.2 i then c else 0)
        else 1 - if x.2 i then c else 0)]
    have hl :
        (∑ x : (Port → Bool) × (Port → Bool), A x.1 * B x.2 *
          ∏ i : Port, if x.1 i then (if x.2 i then c else 0)
            else 1 - if x.2 i then c else 0) = (layerPolynomial A B).eval c := by
      rw [Fintype.sum_prod_type, layerPolynomial_eval]
    rw [hl]
    simp

  let H (y : M → (Port → Bool) × (Port → Bool)) : ℚ :=
    ∏ h : M, A (y h).1 * B (y h).2 *
      ∏ i : Port,
        (if (y h).1 i then (if (y h).2 i then c else 0)
          else 1 - if (y h).2 i then c else 0)
  let V (b : P → Bool) : ℚ := ∏ j : P, (if b j then 1-c else 1) ^ n j
  change (∑ y, ∑ _x : CLayer → Fin q → Bool, ∑ b, H y * V b) = _
  calc
    _ = ∑ y, ∑ _x : CLayer → Fin q → Bool, H y * (∑ b, V b) := by
      simp only [Finset.mul_sum]
    _ = ∑ y, ((∑ _x : CLayer → Fin q → Bool, (1 : ℚ)) *
        (H y * (∑ b, V b))) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (∑ _x : CLayer → Fin q → Bool, (1 : ℚ)) * (∑ y, H y) * (∑ b, V b) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← mul_assoc]
    _ = _ := by
      have hH : (∑ y, H y) = (layerPolynomial A B).eval c ^ Fintype.card M := hm
      have hV : (∑ b, V b) = ∏ j : P, (1 + (1-c) ^ n j) := hp
      rw [hc, hH, hV]

#print axioms planted_layer_factorization

#print axioms layerPolynomial_degree
#print axioms layerPolynomial_eval_one
end LayerPolynomial

#print axioms guarded_count
#print axioms centered_lift_unique
#print axioms recover_from_odd_layer_samples
end LayerRecovery

