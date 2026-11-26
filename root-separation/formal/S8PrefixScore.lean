import S8Prefix
import S8Preprocessing

namespace S8.Prefix

open ProductVariance
open scoped BigOperators

structure Test (P A : Type*) where
  support : Finset P
  check : (support → A) → Bool

variable {P A J : Type*} [Fintype P] [DecidableEq P] [Fintype A] [Nonempty A]

def Test.indicator (test : Test P A) (x : P → A) : ℚ :=
  if test.check (fun p => x p.1) then 1 else 0

def Test.ones (test : Test P A) (free : List P) (fixed : P → A) : ℕ :=
  ∑ x : test.support → A, if test.check (fun p =>
    if p.1 ∈ free then x p else fixed p.1) then 1 else 0

def Test.scaled (test : Test P A) (width : ℕ) (free : List P) (fixed : P → A) : ℕ :=
  test.ones free fixed * Fintype.card A ^ (width - test.support.card)

theorem Test.ones_le (test : Test P A) (free : List P) (fixed : P → A) :
    test.ones free fixed ≤ Fintype.card A ^ test.support.card := by
  calc
    _ ≤ ∑ _ : test.support → A, (1 : ℕ) := Finset.sum_le_sum fun _ _ => by split <;> omega
    _ = _ := by simp [Fintype.card_fun]

theorem Test.scaled_le (test : Test P A) (width : ℕ) (bound : test.support.card ≤ width)
    (free : List P) (fixed : P → A) :
    test.scaled width free fixed ≤ Fintype.card A ^ width := by
  have hh := Nat.mul_le_mul_right (Fintype.card A ^ (width-test.support.card)) (test.ones_le free fixed)
  unfold Test.scaled
  simpa only [← pow_add, Nat.add_sub_of_le bound] using hh

theorem Test.conditional_eq (test : Test P A) (free : List P) (fixed : P → A) :
    conditional test.indicator free fixed =
      (test.ones free fixed : ℚ) / (Fintype.card A : ℚ)^test.support.card := by
  let e : test.support ↪ P := ⟨Subtype.val, Subtype.val_injective⟩
  let f (x : test.support → A) : ℚ := if test.check (fun p =>
    if p.1 ∈ free then x p else fixed p.1) then 1 else 0
  have hm := mean_restrict_primitive e f
  have h : (∑ x, f x) = (test.ones free fixed : ℚ) := by
    unfold Test.ones
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl (fun x _ => by dsimp only [f]; split <;> simp)
  calc
    _ = uniformMean f := hm
    _ = _ := by
      simp only [uniformMean, uniformWeight, Fintype.card_fun, Fintype.card_coe, h,
        Nat.cast_pow, ← div_eq_inv_mul]

theorem Test.scaled_eq (test : Test P A) (width : ℕ) (bound : test.support.card ≤ width)
    (free : List P) (fixed : P → A) :
    (test.scaled width free fixed : ℚ) =
      (Fintype.card A : ℚ)^width * conditional test.indicator free fixed := by
  rw [test.conditional_eq, Test.scaled, Nat.cast_mul, Nat.cast_pow, ← mul_div_assoc]
  apply (eq_div_iff (by positivity)).2
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel bound, mul_comm]

variable [Fintype J]

def score (tests : J → Test P A) (weight : J → ℕ) (width : ℕ)
    (free : List P) (fixed : P → A) : ℕ :=
  ∑ j, weight j * (tests j).scaled width free fixed

def rawScore (tests : J → Test P A) (weight : J → ℕ) (tape : P → A) : ℚ :=
  ∑ j, weight j * (tests j).indicator tape

theorem score_eq (tests : J → Test P A) (weight : J → ℕ) (width : ℕ)
    (bound : ∀ j, (tests j).support.card ≤ width) (free : List P) (fixed : P → A) :
    (score tests weight width free fixed : ℚ) = (Fintype.card A : ℚ)^width *
      conditional (rawScore tests weight) free fixed := by
  have m (j : J) := (tests j).scaled_eq width (bound j) free fixed
  simp only [conditional, rawScore, uniformMean, Finset.sum_mul, Finset.mul_sum,
    score, Nat.cast_sum, Nat.cast_mul] at m ⊢
  rw [Finset.sum_comm (s := (Finset.univ : Finset (P → A)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [m j, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem score_bound (tests : J → Test P A) (weight : J → ℕ) (width cap : ℕ)
    (widthBound : ∀ j, (tests j).support.card ≤ width) (weightBound : ∀ j, weight j ≤ cap)
    (free : List P) (fixed : P → A) :
    score tests weight width free fixed ≤ Fintype.card J * cap * Fintype.card A ^ width := by
  calc
    _ ≤ ∑ _j : J, cap * Fintype.card A ^ width :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul (weightBound j) ((tests j).scaled_le _ (widthBound j) _ _))
    _ = _ := by simp [mul_assoc]

/-- The local integer scores implement the conditional comparison exactly. -/
theorem solve_score_le (tests : J → Test P A) (weight : J → ℕ) (width : ℕ)
    (bound : ∀ j, (tests j).support.card ≤ width)
    (values : List A) (covers : ∀ a, a ∈ values) (fallback : A) (free : List P)
    (nodup : free.Nodup) (fixed : P → A) :
    rawScore tests weight (solve (score tests weight width) values fallback free fixed) ≤
      conditional (rawScore tests weight) free fixed := by
  apply solve_le_conditional _ _ _ _ covers _ _ nodup _
  intro ps x y h
  have h' : (score tests weight width ps x : ℚ) ≤ (score tests weight width ps y : ℚ) := by exact_mod_cast h
  simpa only [score_eq tests weight width bound, mul_le_mul_iff_right₀ (by positivity : 0 <
    (Fintype.card A : ℚ)^width)] using h'

section Agreement
variable {X : Type*} [Fintype X] [DecidableEq A]

def agreement (a b : X → P) : Test P A :=
  let s := Finset.univ.image a ∪ Finset.univ.image b
  ⟨s, fun x => decide (∀ i, x ⟨a i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩ =
    x ⟨b i, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩)⟩

theorem agreement_indicator (a b : X → P) (tape : P → A) :
    (agreement (A := A) a b).indicator tape =
      if tape ∘ a = tape ∘ b then 1 else 0 := by
  classical
  simp [agreement, Test.indicator, funext_iff]

theorem agreement_width (a b : X → P) :
    (agreement (A := A) a b).support.card ≤ 2 * Fintype.card X :=
  (Finset.card_union_le _ _).trans (by
    simpa [two_mul] using Nat.add_le_add
      (Finset.card_image_le (s := (Finset.univ : Finset X)) (f := a))
      (Finset.card_image_le (s := (Finset.univ : Finset X)) (f := b)))

end Agreement

#print axioms Test.conditional_eq
#print axioms score_eq
#print axioms solve_score_le
#print axioms agreement_indicator
#print axioms agreement_width

end S8.Prefix
