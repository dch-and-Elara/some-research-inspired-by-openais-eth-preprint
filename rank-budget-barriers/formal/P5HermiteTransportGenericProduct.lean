import P5HermiteTransportGenericCRT
import P5HermiteTransportGenericShift

/-! Truncated affine multiplication on a real scalar coefficient
vector. Higher coefficients erased by X^k cannot affect a retained
product coefficient, even when the input polynomial is long. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {K : Type*} [Field K]

noncomputable def scalarConvolution {k : ℕ} (c : Fin k→K) : Matrix (Fin k) (Fin k) K :=
  ∑ j : Fin k,c j • shiftMatrix K k j.val

theorem scalarConvolution_block {k : ℕ} (c : Fin k→K) (i j : Fin k) :
    scalarConvolution c i j =
      convolution (fun a=>Matrix.of (fun (_ _ : Unit)=>c a)) (i,()) (j,()) := by
  rw [scalarConvolution,convolution,Matrix.sum_apply,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem scalarConvolution_apply {k : ℕ} (c : Fin k→K) (i j : Fin k) :
    scalarConvolution c i j =
      if _h : j.val ≤ i.val then c ⟨i.val-j.val,(Nat.sub_le _ _).trans_lt i.isLt⟩ else 0 := by
  rw [scalarConvolution_block,convolution_apply]; rfl

set_option maxHeartbeats 6500000 in
theorem affine_product_coeff (t α : K) (k : ℕ) (p q : K[X]) (i : Fin k) :
    scalarObserve t α k (p*q) i =
      (scalarConvolution (scalarObserve t α k p) *ᵥ scalarObserve t α k q) i := by
  let f := affinePolynomial t α p
  let g := affinePolynomial t α q
  let d := polyOfCoeffs k (scalarObserve t α k q)
  have h : (X:K[X])^k ∣ d-g := AdjoinRoot.mk_eq_mk.mp (scalarEncode_observe t α k q)
  have h' : (X:K[X])^k ∣ f*d-f*g := by
    rw [←mul_sub]
    exact dvd_mul_of_dvd_right h f
  have he := Polynomial.X_pow_dvd_iff.mp h' i.val i.isLt
  rw [coeff_sub,sub_eq_zero] at he
  rw [scalarObserve_apply,map_mul]
  change (f*g).coeff i.val=_
  rw [←he,show d=∑j : Fin k,C (scalarObserve t α k q j)*X^j.val from polyOfCoeffs_sum _ _,
    Finset.mul_sum,Polynomial.finset_sum_coeff]
  change (∑j : Fin k, (f*(C (scalarObserve t α k q j)*X^j.val)).coeff i.val) =
    ∑j : Fin k, scalarConvolution (scalarObserve t α k p) i j * scalarObserve t α k q j
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul_X_pow_eq_monomial,Paper5.coeff_mul_monomial_any,scalarConvolution_apply]
  by_cases hh : j.val ≤ i.val
  · rw [if_pos hh,dif_pos hh]; rfl
  · rw [if_neg hh,dif_neg hh]

#print axioms scalarConvolution_block
#print axioms scalarConvolution_apply
#print axioms affine_product_coeff
end Paper5.HermiteGeneric
