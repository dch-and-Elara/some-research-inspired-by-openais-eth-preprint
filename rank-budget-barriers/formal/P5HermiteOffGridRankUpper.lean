import P5HermiteOffGridRankShift
import P5HermiteTransportGenericExpansion

/-! The printed coefficient-capacity bound preceding the exact off-grid
case. This upper bound alone needs no off-grid or window-size hypothesis. -/
namespace Paper5.HermiteOffGrid
open Paper5.HermiteGeneric Matrix
open scoped Classical

variable {K T : Type*} [Field K] [Fintype T] [DecidableEq T]

theorem actual_transfer_rank_le (L : Layout K T) (b : ℕ) (t : T) (j : Fin (L.order t)) :
    (transfer L b t j).rank ≤ min b (L.order t-j.val) := by
  refine le_min ?_ ?_
  · simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (transfer L b t j)
  · unfold transfer
    calc
      _ ≤ (decodeMatrix L b t * shiftMatrix K (L.order t) j.val).rank :=
        Matrix.rank_mul_le_left _ _
      _ ≤ (shiftMatrix K (L.order t) j.val).rank := Matrix.rank_mul_le_right _ _
      _ = _ := truncated_shift_rank _ j

#print axioms actual_transfer_rank_le
end Paper5.HermiteOffGrid
