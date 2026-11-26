import P5MainBalanceM6SparseParity

/-! The actual remainder used by the sparse source is affine in its
argument. Extract both exact integer coefficients without replacing the
source division recurrence. -/
namespace P5MainBalance.M6.Sparse
open Polynomial
open scoped BigOperators Classical Polynomial

theorem quad_natDegree : quad.natDegree=2 := by
  unfold quad
  change (X*(X-C (1:ℤ))).natDegree=2
  rw [natDegree_mul (show (X:ℤ[X])≠0 from X_ne_zero) (X_sub_C_ne_zero 1),natDegree_X,natDegree_X_sub_C]

theorem printed_e_natDegree (ell j : ℕ) : (printedE ell j).natDegree<2 := by
  have hh : quad≠1 := by
    intro h
    have hd := quad_natDegree
    rw [h,natDegree_one] at hd
    omega
  have h := natDegree_modByMonic_lt (((fun p : ℤ[X]=>p /ₘ quad)^[j]) (idempotentPrinted ell))
    quad_monic hh
  simpa only [printedE,quad_natDegree] using h

theorem printed_e_affine (ell j : ℕ) :
    printedE ell j=C ((printedE ell j).coeff 0) + C ((printedE ell j).coeff 1)*X := by
  have h := as_sum_range_C_mul_X_pow' (printedE ell j) (printed_e_natDegree ell j)
  simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,mul_one] using h

theorem printed_e_eval_affine (ell j : ℕ) (y : ℤ) :
    (printedE ell j).eval y=(printedE ell j).coeff 0+(printedE ell j).coeff 1*y := by
  nth_rw 1 [printed_e_affine]
  simp only [eval_add,eval_mul,eval_C,eval_X]

#print axioms quad_natDegree
#print axioms printed_e_natDegree
#print axioms printed_e_affine
#print axioms printed_e_eval_affine
end P5MainBalance.M6.Sparse
