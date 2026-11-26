import P5HermiteWholeFactorQuotient
import P5HermiteWholeFactorConvolution

/-! Lift the furnished left and right factors separately, multiply the
lifts, then truncate its coefficient array. The product is forced to
reduce to the original local matrix and has its original small width. -/
namespace Paper5.HermiteWholeFactor
open Matrix Polynomial
open Paper5.HermiteGeneric (convolution)
open scoped BigOperators Polynomial Classical

variable {R U V W : Type*} [CommRing R]

theorem polynomial_matrix_map_mul {S : Type*} [CommRing S] [Fintype V]
    (f : R[X]→+*S) (A : Matrix U V R[X]) (B : Matrix V W R[X]) :
    (A*B).map f = A.map f * B.map f := by
  apply Matrix.ext
  intro u w
  simp only [Matrix.map_apply,Matrix.mul_apply,map_sum,map_mul]

variable [Fintype V]

noncomputable def liftedProduct (π : R) (P k : ℕ)
    (L : Matrix U V (LocalJet π P k)) (M : Matrix V W (LocalJet π P k)) :
    Matrix U W R[X] :=
  factorLift π P k L * factorLift π P k M

theorem liftedProduct_reduces (π : R) (P k : ℕ)
    (L : Matrix U V (LocalJet π P k)) (M : Matrix V W (LocalJet π P k)) :
    (liftedProduct π P k L M).map (quotientJet π P k) = L*M := by
  unfold liftedProduct
  rw [polynomial_matrix_map_mul,factorLift_recovers,factorLift_recovers]

theorem liftedProduct_permissible (π : R) (P k : ℕ) (C : Fin k→Matrix U W R)
    (L : Matrix U V (LocalJet π P k)) (M : Matrix V W (LocalJet π P k))
    (hFact : finiteJetMatrix π P C = L*M)
    (j : Fin k) (u : U) (w : W) :
    ∃ e : R, truncatedCoefficients (liftedProduct π P k L M) j u w-C j u w = π^P*e := by
  have hR : (liftedProduct π P k L M).map (quotientJet π P k) =
      (jetPolynomialMatrix C).map (quotientJet π P k) := by
    rw [liftedProduct_reduces]
    exact hFact.symm
  have hEntry :
      quotientJet π P k (liftedProduct π P k L M u w) =
        quotientJet π P k (jetPolynomialMatrix C u w) :=
    congrArg (fun A : Matrix U W (LocalJet π P k)=>A u w) hR
  simpa only [truncatedCoefficients,Matrix.of_apply,jetPolynomialMatrix_coeff] using
    quotientJet_coeff_error π P k hEntry j

variable {K : Type*} [Field K] [Algebra R K] [Fintype W]

theorem liftedProduct_rank (π : R) (P k : ℕ)
    (L : Matrix U V (LocalJet π P k)) (M : Matrix V W (LocalJet π P k)) :
    (convolution (fun j : Fin k=>
      (truncatedCoefficients (liftedProduct π P k L M) j).map (algebraMap R K))).rank ≤
      k*Fintype.card V := by
  rw [truncatedCoefficients_map,liftedProduct,polynomial_matrix_map_mul]
  exact polynomial_factor_convolution_rank k _ _

#print axioms polynomial_matrix_map_mul
#print axioms liftedProduct_reduces
#print axioms liftedProduct_permissible
#print axioms liftedProduct_rank
end Paper5.HermiteWholeFactor
