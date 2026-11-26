import J6NativeHeight
import LayerRecovery
import Mathlib.Tactic

/-! Clear the two-input wire factors of the native J6 zero-mode
contraction simultaneously. This is an equality of rationals, not an
assumption about an integer lift or about the delivered residue. -/
namespace J6NativeHeightClearing
open J6NativeHeight
open scoped BigOperators Polynomial
variable {P : Type*} [Fintype P] [DecidableEq P]

theorem entry_cast (n d : ℤ) (hd : d ≠ 0) (y x : Bool) :
    (entry n d y x : ℚ) =
      (d : ℚ) * (LayerRecovery.wireFactor y x).eval ((n:ℚ)/(d:ℚ)) := by
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  cases y <;> cases x <;> simp [entry,LayerRecovery.wireFactor] <;>
    field_simp

noncomputable def rationalSlot (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (c : ℚ) : ℚ :=
  ∑ y : P → Bool, ∑ x : P → Bool,
    if A y && B x then ∏ p, (LayerRecovery.wireFactor (y p) (read p x)).eval c else 0

omit [DecidableEq P] in
theorem cleared_product (n d : ℤ) (hd : d ≠ 0) (y x : P → Bool)
    (read : P → (P → Bool) → Bool) :
    (↑(∏ p, entry n d (y p) (read p x)) : ℚ) =
      (d:ℚ)^Fintype.card P *
        ∏ p, (LayerRecovery.wireFactor (y p) (read p x)).eval ((n:ℚ)/(d:ℚ)) := by
  push_cast
  simp only [entry_cast n d hd,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

theorem explicit_cleared_numerator (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (n d : ℤ) (hd : d ≠ 0) :
    (numerator A B read n d : ℚ) =
      (d:ℚ)^Fintype.card P * rationalSlot A B read ((n:ℚ)/(d:ℚ)) := by
  unfold numerator rationalSlot
  simp only [Int.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (A y && B x) = true
  · simpa [h] using cleared_product n d hd y x read
  · simp [h]

#print axioms entry_cast
#print axioms cleared_product
#print axioms explicit_cleared_numerator
end J6NativeHeightClearing
