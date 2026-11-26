import P5AlwaysSatOriginalCount
import IntegralOutputTransfer
import Mathlib.Algebra.Field.ZMod

/-! An exact layout-free consequence of the original bonus count: its
integer count matrix retains the full-rank parity matrix on any supplied
induced matching. This does not construct that matching for any route. -/
namespace Paper5.AlwaysSatOriginal

variable {V I : Type*} [Fintype V] [Fintype I] {E : Finset (V×V)}

noncomputable def countMatrix (M : PinnedCNF.InducedMatching E I) (T : Finset V)
    (R : Type*) [NatCast R] : Matrix (I→Bool) (I→Bool) R :=
  Matrix.of fun a b=> (PinnedCNF.modelCount (formula E T (M.restrictSigns a b)):R)

theorem matching_residue [DecidableEq I] (M : PinnedCNF.InducedMatching E I) (T : Finset V) :
    (Int.castRingHom (ZMod 2)).mapMatrix (countMatrix M T ℤ)=M.countMatrix (ZMod 2) := by
  ext a b
  let s := M.restrictSigns a b
  change ((PinnedCNF.modelCount (formula E T s):ℤ):ZMod 2)=
    (PinnedCNF.modelCount (PinnedCNF.formula E s):ZMod 2)
  rw [Int.cast_natCast,←ZMod.natCast_mod (PinnedCNF.modelCount (formula E T s)) 2,
    original_count_parity]

theorem matching_rational_cast [DecidableEq I] (M : PinnedCNF.InducedMatching E I) (T : Finset V) :
    (Int.castRingHom ℚ).mapMatrix (countMatrix M T ℤ)=countMatrix M T ℚ := by
  ext a b
  simp [countMatrix]

theorem original_count_full_rank [DecidableEq I] (M : PinnedCNF.InducedMatching E I) (T : Finset V) :
    (countMatrix M T ℚ).rank=2^Fintype.card I := by
  classical
  have hh := IntegralOutputTransfer.full_rank_of_residue (Int.castRingHom ℚ)
    (Int.castRingHom (ZMod 2)) Int.cast_injective (countMatrix M T ℤ)
    (M.countMatrix (ZMod 2)) (matching_residue M T)
    (M.countMatrix_det_isUnit (ZMod 2)).ne_zero
  rw [matching_rational_cast] at hh
  simpa using hh

#print axioms matching_residue
#print axioms matching_rational_cast
#print axioms original_count_full_rank
end Paper5.AlwaysSatOriginal