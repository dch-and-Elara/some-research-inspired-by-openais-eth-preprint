import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Finite-precision reconstruction and the residue-to-field rank bridge.
The precision hypotheses describe each local replacement error and the
denominators of the fixed reconstruction coefficients. No additive section
of a residue map is assumed. -/

namespace IntegralOutputTransfer

open scoped BigOperators

section Reconstruction

variable {R K : Type*} [CommRing R] [CommRing K]
variable {J : Type*} [Fintype J]

theorem weighted_lift_identity (embed : R →+* K) (pi : R) (p : ℕ)
    (q : J → ℕ) (original replacement : J → R) (coefficient : J → K)
    (cleared error : J → R) (target : R)
    (herr : ∀ j, replacement j = original j + pi ^ q j * error j)
    (hclear : ∀ j, coefficient j * embed (pi ^ q j) = embed (pi ^ p * cleared j))
    (hexact : ∑ j, coefficient j * embed (original j) = embed target) :
    (∑ j, coefficient j * embed (replacement j)) =
      embed (target + pi ^ p * ∑ j, cleared j * error j) := by
  have hterm (j : J) : coefficient j * embed (replacement j) =
      coefficient j * embed (original j) + embed (pi ^ p * (cleared j * error j)) := by
    rw [herr j, map_add, mul_add, map_mul, ← mul_assoc, hclear j]
    simp only [map_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, hexact, ← map_sum, ← Finset.mul_sum, ← map_add]

theorem reconstructed_residue {S : Type*} [CommRing S]
    (residue : R →+* S) (pi target error : R) (p : ℕ)
    (hpi : residue pi = 0) (hp : 0 < p) :
    residue (target + pi ^ p * error) = residue target := by
  simp [hpi, ne_of_gt hp]

theorem exists_integral_reconstruction {S : Type*} [CommRing S]
    (embed : R →+* K) (residue : R →+* S) (pi : R) (p : ℕ)
    (q : J → ℕ) (original replacement : J → R) (coefficient : J → K)
    (cleared error : J → R) (target : R)
    (herr : ∀ j, replacement j = original j + pi ^ q j * error j)
    (hclear : ∀ j, coefficient j * embed (pi ^ q j) = embed (pi ^ p * cleared j))
    (hexact : ∑ j, coefficient j * embed (original j) = embed target)
    (hpi : residue pi = 0) (hp : 0 < p) :
    ∃ output : R,
      (∑ j, coefficient j * embed (replacement j)) = embed output ∧
      residue output = residue target := by
  refine ⟨target + pi ^ p * ∑ j, cleared j * error j, ?_, ?_⟩
  · exact weighted_lift_identity embed pi p q original replacement coefficient
      cleared error target herr hclear hexact
  · exact reconstructed_residue residue pi target (∑ j, cleared j * error j) p hpi hp

end Reconstruction

section Rank

variable {R S K n : Type*} [CommRing R] [CommRing S] [Field K]
variable [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_residue (residue : R →+* S)
    (M : Matrix n n R) (target : Matrix n n S)
    (hresidue : residue.mapMatrix M = target) (htarget : target.det ≠ 0) :
    M.det ≠ 0 := by
  intro hz
  apply htarget
  rw [← hresidue, ← residue.map_det, hz, map_zero]

theorem det_embedding_ne_zero (embed : R →+* K)
    (hinjective : Function.Injective embed) (M : Matrix n n R) (hdet : M.det ≠ 0) :
    (embed.mapMatrix M).det ≠ 0 := by
  rw [← embed.map_det]
  intro hz
  apply hdet
  apply hinjective
  simpa only [map_zero] using hz

theorem full_rank_of_residue (embed : R →+* K) (residue : R →+* S)
    (hinjective : Function.Injective embed)
    (M : Matrix n n R) (target : Matrix n n S)
    (hresidue : residue.mapMatrix M = target) (htarget : target.det ≠ 0) :
    (embed.mapMatrix M).rank = Fintype.card n := by
  apply Matrix.rank_of_isUnit
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr
    (det_embedding_ne_zero embed hinjective M
      (det_ne_zero_of_residue residue M target hresidue htarget))

theorem sum_full_rank_of_residue {J : Type*} [Fintype J]
    (embed : R →+* K) (residue : R →+* S)
    (hinjective : Function.Injective embed)
    (M : Matrix n n R) (target : Matrix n n S) (terms : J → Matrix n n K)
    (hrepresentation : (∑ j, terms j) = embed.mapMatrix M)
    (hresidue : residue.mapMatrix M = target) (htarget : target.det ≠ 0) :
    (∑ j, terms j).rank = Fintype.card n := by
  rw [hrepresentation]
  exact full_rank_of_residue embed residue hinjective M target hresidue htarget

end Rank

#print axioms weighted_lift_identity
#print axioms reconstructed_residue
#print axioms exists_integral_reconstruction
#print axioms det_ne_zero_of_residue
#print axioms det_embedding_ne_zero
#print axioms full_rank_of_residue
#print axioms sum_full_rank_of_residue

end IntegralOutputTransfer
