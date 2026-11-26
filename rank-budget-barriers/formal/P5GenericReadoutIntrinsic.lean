import P5GenericReadoutPair
import Mathlib.LinearAlgebra.Dual.Basis

/-! The quantity rho is literally the rank of the map into the dual,
not a new basis-dependent proxy. -/
namespace Paper5.GenericReadout
open Matrix Module
open scoped BigOperators Classical

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

noncomputable def rho (read : A→ₗ[K]K) : ℕ :=
  Module.finrank K (LinearMap.range (multiplicationPair read))

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem pairing_matrix (b : Basis J K A) (read : A→ₗ[K]K) :
    LinearMap.toMatrix b b.dualBasis (multiplicationPair read) = P5A2.pairing b read := by
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply,Basis.dualBasis_repr,multiplicationPair_apply]
  exact congrArg read (mul_comm (b j) (b i))

theorem capacity_eq_rho (b : Basis J K A) (read : A→ₗ[K]K) :
    capacity b read = rho read := by
  unfold capacity rho
  rw [←pairing_matrix b read,Matrix.rank_eq_finrank_range_toLin _ b.dualBasis b,
    Matrix.toLin_toMatrix]

omit [Fintype J] [DecidableEq J] in
theorem exact_intrinsic_readout_capacity [FiniteDimensional K A] (read : A→ₗ[K]K) :
    Realizes read (rho read) ∧
      (∀r,Realizes read r → rho read≤r) ∧ rho read≤Module.finrank K A := by
  let b := Module.finBasis K A
  rw [←capacity_eq_rho b read]
  exact exact_readout_capacity b read

#print axioms pairing_matrix
#print axioms capacity_eq_rho
#print axioms exact_intrinsic_readout_capacity
end Paper5.GenericReadout
