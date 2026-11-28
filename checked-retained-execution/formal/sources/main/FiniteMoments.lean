import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The finite dominated-variance step. The comparison measure need not have
the same mean as the original measure. -/

namespace FiniteMoments

open scoped BigOperators

variable {E : Type*} [Fintype E]

theorem centered_square_identity (mu y : E → ℚ) (a : ℚ)
    (hm : ∑ e, mu e = 1) (hy : ∑ e, mu e * y e = 0) :
    (∑ e, mu e * (y e - a) ^ 2) = (∑ e, mu e * y e ^ 2) + a ^ 2 := by
  have hpoint (e : E) : mu e * (y e - a) ^ 2 =
      mu e * y e ^ 2 - 2 * a * (mu e * y e) + a ^ 2 * mu e := by ring
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hm, hy, mul_zero, sub_zero, mul_one]

theorem centered_square_le (mu y : E → ℚ) (a : ℚ)
    (hm : ∑ e, mu e = 1) (hy : ∑ e, mu e * y e = 0) :
    (∑ e, mu e * y e ^ 2) ≤ ∑ e, mu e * (y e - a) ^ 2 := by
  rw [centered_square_identity mu y a hm hy]
  exact le_add_of_nonneg_right (sq_nonneg a)

theorem dominated_centered_second_moment (mu nu y : E → ℚ) (C a : ℚ)
    (hm : ∑ e, mu e = 1) (hy : ∑ e, mu e * y e = 0)
    (hdom : ∀ e, mu e ≤ C * nu e) :
    (∑ e, mu e * y e ^ 2) ≤ C * ∑ e, nu e * (y e - a) ^ 2 := by
  calc
    _ ≤ ∑ e, mu e * (y e - a) ^ 2 := centered_square_le mu y a hm hy
    _ ≤ ∑ e, (C * nu e) * (y e - a) ^ 2 := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_right (hdom e) (sq_nonneg _)
    _ = _ := by simp only [mul_assoc, Finset.mul_sum]

#print axioms centered_square_identity
#print axioms centered_square_le
#print axioms dominated_centered_second_moment

end FiniteMoments
