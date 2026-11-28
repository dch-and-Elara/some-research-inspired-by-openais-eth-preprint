import V8NativeMessageN6MainFiberPrinted
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import JointContraction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

/-! Coefficient readout from the actual truncated MAIN quotient.  No
unobserved polynomial representative or extra answer is used. -/
namespace J3R38LiteralSingleton
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Polynomial BigOperators Classical

noncomputable section

def jetCoeff {J : ℕ} (k : ℕ) (a : Jet J) : ℚ :=
  (AdjoinRoot.modByMonicHom (monic_X.pow J) a).coeff k

theorem jetCoeff_mk {J k : ℕ} (hk : k < J) (p : ℚ[X]) :
    jetCoeff k (AdjoinRoot.mk ((X:ℚ[X])^J) p) = p.coeff k := by
  rw [jetCoeff, AdjoinRoot.modByMonicHom_mk, modByMonic_eq_sub_mul_div _ (monic_X.pow J),
    coeff_sub]
  have hz : (((X:ℚ[X])^J) * (p /ₘ ((X:ℚ[X])^J))).coeff k = 0 := by
    rw [coeff_X_pow_mul']
    simp [Nat.not_le_of_gt hk]
  simp [hz]

theorem joint_constant_ne_zero {V : Type*} [Fintype V]
    (B : ℚ[X]) (p : V→ℚ[X]) (s : V→Bool)
    (hB : B.coeff 0≠0) (h0 : ∀ v,(p v).coeff 0≠0) (h1 : ∀ v,(p v).coeff 0≠1) :
    (B * ∏ v, JointContraction.pinPolynomial (s v) (p v)).coeff 0 ≠ 0 := by
  rw [mul_coeff_zero, coeff_zero_prod]
  refine mul_ne_zero hB (Finset.prod_ne_zero_iff.mpr ?_)
  intro v _
  cases hs : s v
  · simpa [JointContraction.pinPolynomial,sub_ne_zero] using Ne.symm (h1 v)
  · simpa [JointContraction.pinPolynomial] using h0 v

theorem comp_affine_coeff_zero (p : ℚ[X]) (t : ℚ) :
    (p.comp (C t+X)).coeff 0 = p.eval t := by
  rw [coeff_zero_eq_eval_zero,eval_comp]
  simp

theorem comp_affine_coeff_one (p : ℚ[X]) (t : ℚ) :
    (p.comp (C t+X)).coeff 1 = p.derivative.eval t := by
  have hc (q : ℚ[X]) : q.derivative.eval 0 = q.coeff 1 := by
    simp [← coeff_zero_eq_eval_zero,coeff_derivative]
  rw [← hc, derivative_comp]
  simp [eval_comp]

#print axioms comp_affine_coeff_zero
#print axioms comp_affine_coeff_one
#print axioms jetCoeff_mk
#print axioms joint_constant_ne_zero

end
end J3R38LiteralSingleton
