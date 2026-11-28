import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The actual polynomial quotient by X^k and its monomial basis;
products crossing the truncation boundary vanish in the ring itself. -/
namespace P5A2
open Polynomial Matrix Module
open scoped Classical BigOperators

abbrev Trunc (R : Type*) [CommRing R] (k : ℕ) := AdjoinRoot ((X : R[X])^k)

section Powers
variable (R : Type*) [CommRing R] [Nontrivial R]

/-- No assumption that the coefficient ring is a domain. This applies to
the second truncation over a nonreduced first jet ring. -/
noncomputable def powers (k : ℕ) : Basis (Fin k) R (Trunc R k) :=
  (AdjoinRoot.powerBasis' ((monic_X : (X : R[X]).Monic).pow k)).basis.reindex
    (finCongr (natDegree_X_pow k))

theorem powers_apply (k : ℕ) (i : Fin k) :
    powers R k i = AdjoinRoot.mk ((X : R[X])^k) ((X : R[X])^i.val) := by
  unfold powers
  rw [Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' ((monic_X : (X : R[X]).Monic).pow k)).basis_eq_pow]
  rw [(AdjoinRoot.mk _).map_pow,AdjoinRoot.mk_X]
  rfl

theorem powers_mul (k : ℕ) (i j : Fin k) :
    powers R k i * powers R k j =
      if h : i.val+j.val<k then powers R k ⟨i.val+j.val,h⟩ else 0 := by
  rw [powers_apply,powers_apply,← map_mul,← pow_add]
  split
  · rw [powers_apply]
  · rename_i hi
    exact AdjoinRoot.mk_eq_zero.mpr (pow_dvd_pow _ (Nat.le_of_not_gt hi))

theorem trunc_nontrivial (k : ℕ) (hk : 0<k) : Nontrivial (Trunc R k) := by
  have hz : eval₂ (RingHom.id R) (0:R) ((X : R[X])^k) = 0 := by simp [hk.ne']
  let e : Trunc R k →+* R := AdjoinRoot.lift (RingHom.id R) 0 hz
  have h : (1 : Trunc R k) ≠ 0 := by
    intro hn
    have h' := congrArg e hn
    exact one_ne_zero (by simpa only [map_one,map_zero] using h')
  exact nontrivial_of_ne 1 0 h
end Powers

/-- The actual multiplication pairing in a fixed basis. -/
noncomputable def pairing {K A J : Type*} [Field K] [CommRing A] [Algebra K A]
    (b : Basis J K A) (read : A →ₗ[K] K) : Matrix J J K :=
  Matrix.of fun i j => read (b i*b j)

theorem coord_basis {K A J : Type*} [Field K] [AddCommGroup A] [Module K A]
    (b : Basis J K A) (i j : J) :
    b.coord i (b j) = if j=i then 1 else 0 := by
  rw [Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]

#print axioms powers_apply
#print axioms powers_mul
#print axioms trunc_nontrivial
#print axioms coord_basis
end P5A2
