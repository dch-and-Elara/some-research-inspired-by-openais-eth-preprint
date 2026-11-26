import P5HermiteOffGridRankAffine
import P5HermiteOffGridRankDecode
import P5HermiteOffGridRankShift

/-! Exact original rank of G_tj, for the off-grid anchor and b>=k_t.
The map is the SAME transfer built and used in the verified H.1–H.3. -/
namespace Paper5.HermiteOffGrid
open Paper5.HermiteGeneric Matrix Module
open scoped BigOperators Classical

variable {K U V W : Type*} [Field K] [Fintype U] [Fintype V] [Fintype W]

omit [Fintype U] in
theorem rank_right_surjective (X : Matrix U V K) (E : Matrix V W K)
    (hE : Function.Surjective E.mulVecLin) : (X*E).rank=X.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul,LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hE)]

omit [Fintype U] in
theorem rank_left_injective (D : Matrix U V K) (X : Matrix V W K)
    (hD : Function.Injective D.mulVecLin) : (D*X).rank=X.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_mul,LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective D.mulVecLin hD (LinearMap.range X.mulVecLin)).finrank_eq.symm

variable {T : Type*} [Fintype T] [DecidableEq T]

theorem actual_off_grid_transfer_rank (L : Layout K T) (b : ℕ) (t : T)
    (ht : 0<L.order t) (hb : L.order t≤b)
    (hOff : ∀s,L.anchor≠L.center s) (j : Fin (L.order t)) :
    (transfer L b t j).rank=L.order t-j.val := by
  unfold transfer
  rw [rank_right_surjective _ _ (actual_input_surjective L b t ht hb),
    rank_left_injective _ _ (actual_decode_injective L b t hOff hb)]
  exact truncated_shift_rank _ j

#print axioms rank_right_surjective
#print axioms rank_left_injective
#print axioms actual_off_grid_transfer_rank
end Paper5.HermiteOffGrid
