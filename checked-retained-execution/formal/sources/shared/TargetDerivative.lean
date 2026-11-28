import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# First coefficient at the target of a source singleton mode

These are the finite polynomial and sign steps of J8. The target set and its
local arguments are supplied; the source packing that gives them is not part
of these definitions.
-/

open scoped BigOperators Classical

namespace TargetDerivative

noncomputable section

section PolynomialSteps

variable {R I : Type*} [CommRing R]

def bitFactor (b : Bool) (x : R) : R := if b then x else 1 - x

/-- The two-leg multilinear extension of the two-bit equality table. -/
def equality (x y : R) : R := (1 - x) * (1 - y) + x * y

theorem equality_as_table_sum (x y : R) :
    (∑ a : Bool, ∑ b : Bool, if a = b then bitFactor a x * bitFactor b y else 0) =
      equality x y := by
  simp [bitFactor, equality]
  ac_rfl

/-- Vary just the selected leg of one subdivision equality. This is the
multiaffine identity behind the factor replacement in J8. -/
theorem equality_target_leg (x y increment : R) :
    equality (x + increment) y = equality x y + increment * (-1 + 2 * y) := by
  unfold equality
  ring

theorem first_mul_vanishing_target (p q : Polynomial R) (h : p.coeff 0 = 0) :
    (p * q).coeff 1 = p.coeff 1 * q.coeff 0 := by
  simp [Polynomial.mul_coeff_one, h]

/-- If each selected target kernel vanishes at zero, no derivative of a
baseline factor contributes to first order, including the source child. -/
theorem first_completed_target (s : Finset I)
    (publicProduct sourceMoment : Polynomial R) (kernel alteredTarget : I → Polynomial R)
    (vanish : ∀ x ∈ s, (kernel x).coeff 0 = 0) :
    (((publicProduct * sourceMoment) *
      ∑ x ∈ s, kernel x * alteredTarget x).coeff 1) =
      (publicProduct.coeff 0 *
        ∑ x ∈ s, (kernel x).coeff 1 * (alteredTarget x).coeff 0) *
      sourceMoment.coeff 0 := by
  have h0 : (∑ x ∈ s, kernel x * alteredTarget x).coeff 0 = 0 := by
    rw [Polynomial.finset_sum_coeff]
    exact Finset.sum_eq_zero fun x hx => by simp [vanish x hx]
  have h1 : (∑ x ∈ s, kernel x * alteredTarget x).coeff 1 =
      ∑ x ∈ s, (kernel x).coeff 1 * (alteredTarget x).coeff 0 := by
    rw [Polynomial.finset_sum_coeff]
    exact Finset.sum_congr rfl fun x hx =>
      first_mul_vanishing_target (kernel x) (alteredTarget x) (vanish x hx)
  rw [Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, h0, h1, mul_zero, add_zero]
  ac_rfl

end PolynomialSteps

section StrictSign

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Even when both baseline legs are nonpositive the ordinary equality
factor is strictly positive; the one-matched-leg case is a specialization. -/
theorem baseline_equality_positive (x y : K) (hx : x ≤ 0) (hy : y ≤ 0) :
    0 < equality x y := by
  have hx' : 0 < 1 - x := by linarith
  have hy' : 0 < 1 - y := by linarith
  exact add_pos_of_pos_of_nonneg (mul_pos hx' hy') (mul_nonneg_of_nonpos_of_nonpos hx hy)

theorem target_derivative_negative (w : K) (h : w ≤ 0) : -1 + 2 * w < 0 := by
  linarith

/-- The explicit Cauchy target slope is negative when the outer probe
weight is negative and the indicated odd denominator is positive. -/
theorem target_kernel_slope_negative (c alpha denom : K) (b : ℕ)
    (hc : c < 0) (ha : 0 < alpha) (hd : 0 < denom) :
    c * alpha * (2 : K) ^ b / denom ^ (b + 1) < 0 := by
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hc ha) (pow_pos (by norm_num) b))
    (pow_pos hd (b + 1))

/-- A zero-mode sibling is positive under the same column-acceptance
conditions. This includes an empty list of subdivision vertices. -/
theorem baseline_sum_positive {X J : Type*} [Fintype X] [Fintype J]
    (weight : X → K) (row₁ row₂ : X → J → K)
    (column_nonnegative : ∀ x, 0 ≤ weight x)
    (exists_column : ∃ x, 0 < weight x)
    (rows₁_nonpositive : ∀ x j, row₁ x j ≤ 0)
    (rows₂_nonpositive : ∀ x j, row₂ x j ≤ 0) :
    0 < ∑ x, weight x * ∏ j, equality (row₁ x j) (row₂ x j) := by
  have hrows (x : X) : 0 < ∏ j, equality (row₁ x j) (row₂ x j) :=
    Finset.prod_pos fun j _ =>
      baseline_equality_positive _ _ (rows₁_nonpositive x j) (rows₂_nonpositive x j)
  obtain ⟨x, hx⟩ := exists_column
  exact Finset.sum_pos' (fun y _ => mul_nonneg (column_nonnegative y) (hrows y).le)
    ⟨x, Finset.mem_univ x, mul_pos hx (hrows x)⟩

/-- The genuine signed target sum is strictly negative with nonnegative
column weights and at least one accepted column assignment. No generic
noncancellation assumption is used. -/
theorem alteredTarget_negative {X J : Type*} [Fintype X] [Fintype J]
    (weight otherLeg : X → K) (row₁ row₂ : X → J → K)
    (column_nonnegative : ∀ x, 0 ≤ weight x)
    (exists_column : ∃ x, 0 < weight x)
    (other_nonpositive : ∀ x, otherLeg x ≤ 0)
    (rows₁_nonpositive : ∀ x j, row₁ x j ≤ 0)
    (rows₂_nonpositive : ∀ x j, row₂ x j ≤ 0) :
    (∑ x, weight x * (-1 + 2 * otherLeg x) *
      ∏ j, equality (row₁ x j) (row₂ x j)) < 0 := by
  let val : X → K := fun x =>
    weight x * (-1 + 2 * otherLeg x) * ∏ j, equality (row₁ x j) (row₂ x j)
  have hrows (x : X) : 0 < ∏ j, equality (row₁ x j) (row₂ x j) :=
    Finset.prod_pos fun j _ =>
      baseline_equality_positive _ _ (rows₁_nonpositive x j) (rows₂_nonpositive x j)
  have hall (x : X) : val x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (column_nonnegative x)
      (target_derivative_negative _ (other_nonpositive x)).le) (hrows x).le
  obtain ⟨x, hx⟩ := exists_column
  have hone : val x < 0 := mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hx (target_derivative_negative _ (other_nonpositive x))) (hrows x)
  change (∑ x, val x) < 0
  apply neg_pos.mp
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_pos' (fun y _ => neg_nonneg.mpr (hall y))
    ⟨x, Finset.mem_univ x, neg_pos.mpr hone⟩

/-- With at least one eligible real target, strict negative slopes and strict
negative altered targets yield a strictly positive compiled multiplier. -/
theorem completed_scale_positive {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (publicConstant : K) (slope target : I → K)
    (baselines : 0 < publicConstant)
    (kernel_negative : ∀ x ∈ s, slope x < 0)
    (target_negative : ∀ x ∈ s, target x < 0) :
    0 < publicConstant * ∑ x ∈ s, slope x * target x :=
  mul_pos baselines
    (Finset.sum_pos (fun x hx => mul_pos_of_neg_of_neg (kernel_negative x hx) (target_negative x hx)) hs)

end StrictSign

#print axioms equality_as_table_sum
#print axioms equality_target_leg
#print axioms first_mul_vanishing_target
#print axioms first_completed_target
#print axioms baseline_equality_positive
#print axioms target_derivative_negative
#print axioms target_kernel_slope_negative
#print axioms baseline_sum_positive
#print axioms alteredTarget_negative
#print axioms completed_scale_positive

end

end TargetDerivative
