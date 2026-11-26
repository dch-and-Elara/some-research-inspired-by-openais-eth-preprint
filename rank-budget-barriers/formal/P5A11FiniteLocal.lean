import P5A11JetCoordinate
import P5A11CoeffCoker

/-! The honest finite jet cokernel is the cokernel of the reduction of an
ordinary integral convolution matrix. Quotient formation commutes with
the explicit coefficient-coordinate change. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

section Conjugacy
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem range_map_conjugate (e : M ≃ₗ[R] N) (F : M→ₗ[R] M) (G : N→ₗ[R] N)
    (h : ∀ x,e (F x)=G (e x)) : (LinearMap.range F).map e.toLinearMap = LinearMap.range G := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    exact ⟨e x,(h x).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := e.surjective z
    exact ⟨F x,⟨x,rfl⟩,h x⟩

noncomputable def range_conjugate_equiv (e : M ≃ₗ[R] N) (F : M→ₗ[R] M) (G : N→ₗ[R] N)
    (h : ∀ x,e (F x)=G (e x)) : LinearMap.range F ≃ₗ[R] LinearMap.range G := by
  let E := Submodule.equivMapOfInjective e.toLinearMap e.injective (LinearMap.range F)
  rw [range_map_conjugate e F G h] at E
  exact E
end Conjugacy

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def localCoefficientMatrix (A : Matrix I I R[X]) (t α : R) (k : ℕ) :
    Matrix (I × Fin k) (I × Fin k) R :=
  coefficientMatrix (A.map (affinePolynomial t α)) k k

omit [DecidableEq I] [Fintype I] in
theorem localCoefficientMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R[X]) (t α : R) (k : ℕ) :
    (localCoefficientMatrix A t α k).map f =
      localCoefficientMatrix (A.map (Polynomial.mapRingHom f)) (f t) (f α) k := by
  unfold localCoefficientMatrix
  rw [coefficientMatrix_map]
  congr 1
  apply Matrix.ext
  intro i j
  change ((A i j).comp (C t + C α * X)).map f =
    ((A i j).map f).comp (C (f t) + C (f α) * X)
  rw [Polynomial.map_comp,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,Polynomial.map_X]

omit [DecidableEq I] in
theorem finite_local_coordinate_commutes (A : Matrix I I R[X]) (π t α : R) (P k : ℕ)
    (x : I × Fin k→Cyclic π P) :
    (jetCoordinates k).restrictScalars R (finiteCoeffMatrix π P (localCoefficientMatrix A t α k) x) =
      localMul A π t α P k ((jetCoordinates k).restrictScalars R x) := by
  let ρ := Ideal.Quotient.mk (PowIdeal π P)
  let B := (A.map (affinePolynomial t α)).map (Polynomial.mapRingHom ρ)
  change encodeJet k (((localCoefficientMatrix A t α k).map ρ) *ᵥ x) =
    A.map (nativeObs π t α P k).toRingHom *ᵥ encodeJet k x
  have hB : (localCoefficientMatrix A t α k).map ρ = coefficientMatrix B k k := by
    unfold localCoefficientMatrix
    rw [coefficientMatrix_map]
  rw [hB,encodeJet_commutes]
  congr 1
  ext i j
  change AdjoinRoot.mk (X^k) (((affinePolynomial t α) (A i j)).map ρ) =
    (nativeObs π t α P k).toRingHom (A i j)
  rw [nativeObs_as_affine]
  rfl

variable [IsDomain R] [IsLocalRing R]

theorem real_jet_coker_le (A : Matrix I I R[X]) (π t α : R) (P k : ℕ)
    (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal) :
    Module.length R ((I→LocalJet π P k) ⧸ LinearMap.range (localMul A π t α P k)) ≤
      ((Fintype.card I*k - ((localCoefficientMatrix A t α k).map (IsLocalRing.residue R)).rank)*P : ℕ) := by
  let E := (jetCoordinates (S:=Cyclic π P) (I:=I) k).restrictScalars R
  let M := localCoefficientMatrix A t α k
  let F := finiteCoeffMatrix π P M
  let G := localMul A π t α P k
  have J := Submodule.Quotient.equiv (LinearMap.range F) (LinearMap.range G) E
    (range_map_conjugate E F G (finite_local_coordinate_commutes A π t α P k))
  have h := coker_matrix_reduction_bound π hπ hmax P M
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  exact J.length_eq.symm.trans_le h

#print axioms range_map_conjugate
#print axioms range_conjugate_equiv
#print axioms localCoefficientMatrix_map
#print axioms finite_local_coordinate_commutes
#print axioms real_jet_coker_le
end Paper5
