import V8CapacitySmithModules
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Instantiate the observable Smith module using the genuine image of
an arbitrary finite coefficient/evaluation matrix, not an assumed
diagonal model. This is the algebraic matrix step of A4. -/
namespace V8CapacitySmith
open scoped Classical BigOperators
open V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {O I J : Type*} [CommRing O] [IsDomain O]
variable [IsLocalRing O] [IsPrincipalIdealRing O]
variable [Fintype I] [Fintype J] [DecidableEq I]

abbrev matrixImage (A : Matrix I J O) : Submodule O (I → O) :=
  LinearMap.range A.mulVecLin

def matrixPowered (π : O)
    (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (A : Matrix I J O) : Σ n, Powered π (matrixImage A) I n :=
  exists_powered π hMax (Pi.basisFun O I) (matrixImage A)

theorem exact_raw_matrix_membership (π : O)
    (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (A : Matrix I J O) (b : I → O) :
    let S := (matrixPowered π hMax A).2
    (∃ x : J → O, A.mulVec x=b) ↔
      (∀ i, π^(S.exponent i)∣coord S b (S.chart.f i)) ∧
      (∀ j : I, j∉Set.range S.chart.f → coord S b j=0) :=
  exact_membership (matrixPowered π hMax A).2 b

def matrixA4 (π : O)
    (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (hπ : π≠0) (A : Matrix I J O) (L p : ℕ) :
    let S := (matrixPowered π hMax A).2
    ((i : Fin (matrixPowered π hMax A).1) → BaseMod O π (p-clipped S L p i)) ≃ₗ[O]
      observed S L p :=
  A4_modules (matrixPowered π hMax A).2 L p hπ

#print axioms matrixPowered
#print axioms exact_raw_matrix_membership
#print axioms matrixA4
end
end V8CapacitySmith
