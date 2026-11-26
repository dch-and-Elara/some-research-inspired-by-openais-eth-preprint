import P5HermiteTransportGenericProduct
import P5HermiteTransportGenericExpansion

/-! Literal source correspondence for L_t: coefficient-first
convolution is multiplication in the actual quotient K[z]/(z^k),
including arbitrary replacement coefficient matrices. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {K U V : Type*} [Field K]

theorem affine_zero_one (p : K[X]) : affinePolynomial 0 1 p=p := by
  change p.comp (C (0:K)+C (1:K)*X)=p
  rw [map_zero,map_one,zero_add,one_mul,comp_X]

theorem rawObserve_polyOfCoeffs (k : ℕ) (x : Fin k→K) :
    scalarObserve 0 1 k (polyOfCoeffs k x)=x := by
  funext i
  rw [scalarObserve_apply,affine_zero_one,polyOfCoeffs_coeff]

theorem scalarConvolution_actual_jet {k : ℕ} (c x : Fin k→K) :
    scalarEncode k (scalarConvolution c *ᵥ x)=scalarEncode k c*scalarEncode k x := by
  let p := polyOfCoeffs k c
  let q := polyOfCoeffs k x
  have h : scalarObserve 0 1 k (p*q)=scalarConvolution c *ᵥ x := by
    funext i
    rw [affine_product_coeff]
    change (scalarConvolution (scalarObserve 0 1 k (polyOfCoeffs k c)) *ᵥ
      scalarObserve 0 1 k (polyOfCoeffs k x)) i=_
    rw [rawObserve_polyOfCoeffs,rawObserve_polyOfCoeffs]
  rw [←h,scalarEncode_observe,affine_zero_one,map_mul]; rfl

noncomputable def honestJetMatrix {k : ℕ} (C : Fin k→Matrix U V K) :
    Matrix U V (PlainJet K k) :=
  Matrix.of fun u v=>scalarEncode k (fun i=>C i u v)

theorem true_hasse_jet_matrix (A : Matrix U V K[X]) (t a : K) (k : ℕ) :
    honestJetMatrix (observedCoefficients A t a k) =
      A.map ((AdjoinRoot.mk (X^k : K[X])).comp (affinePolynomial t a)) := by
  ext u v
  exact scalarEncode_observe t a k (A u v)

variable [Fintype V]
set_option maxHeartbeats 8000000 in
theorem coefficient_first_actual_L {k : ℕ} (C : Fin k→Matrix U V K)
    (x : Fin k × V→K) (u : U) :
    scalarEncode k (fun i=>(convolution C *ᵥ x) (i,u)) =
      (honestJetMatrix C *ᵥ fun v=>scalarEncode k (fun j=>x (j,v))) u := by
  have h : (fun i=>(convolution C *ᵥ x) (i,u)) =
      ∑ v, scalarConvolution (fun j=>C j u v) *ᵥ (fun j=>x (j,v)) := by
    funext i
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro j _
    rw [convolution_apply,scalarConvolution_apply]
  rw [h,map_sum]
  simp only [scalarConvolution_actual_jet,Matrix.mulVec,dotProduct,honestJetMatrix,Matrix.of_apply]

#print axioms scalarConvolution_actual_jet
#print axioms true_hasse_jet_matrix
#print axioms coefficient_first_actual_L
end Paper5.HermiteGeneric
