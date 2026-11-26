import P5HermiteTransportGenericAnchor
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Choose an actual nonzero maximal-rank minor over a field, including
for a rectangular matrix. No supplied minor-selection receipt. -/
namespace Paper5.HermiteGeneric
open Matrix Module
open scoped BigOperators Classical

variable {K U V X Y : Type*} [Field K] [Fintype U] [Fintype V]

omit [Fintype U] in
theorem submatrix_rank_mono [Fintype Y] (A : Matrix U V K) (r : X→U) (c : Y→V) :
    (A.submatrix r c).rank≤A.rank := by
  have hA : A.eRank≠⊤ := by
    apply ne_top_of_le_ne_top _ A.eRank_le_card_width
    simp
  simpa only [Matrix.eRank_toNat_eq_rank] using ENat.toNat_le_toNat (A.eRank_submatrix_le r c) hA

theorem spanning_columns (A : Matrix U V K) :
    ∃ c : Fin A.rank ↪ V,(A.submatrix id c).rank=A.rank := by
  have h := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  rw [←Matrix.rank_eq_finrank_span_cols] at h
  obtain ⟨f,hf,hspan,hi⟩ := h
  choose c hc using hf
  have hI : Function.Injective c := fun a b h=>hi.injective ((hc a).symm.trans
    (congrArg A.col h |>.trans (hc b)))
  let e : Fin A.rank ↪ V := ⟨c,hI⟩
  refine ⟨e,?_⟩
  have hs : (A.submatrix id e).col=f := by
    funext i
    exact hc i
  rw [Matrix.rank_eq_finrank_span_cols,hs,hspan,←Matrix.rank_eq_finrank_span_cols]

omit [Fintype U] [Fintype V] in
theorem square_full_rank_det {Z : Type*} [Fintype Z] [DecidableEq Z]
    (A : Matrix Z Z K) (h : A.rank=Fintype.card Z) : A.det≠0 := by
  have hr : LinearMap.range A.mulVecLin=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_pi] using h
  have hi : Function.Injective A.mulVecLin :=
    LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp hr)
  intro hD
  obtain ⟨x,hx,h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hD
  apply hx
  apply hi
  change A *ᵥ x=A *ᵥ 0
  rw [h0,Matrix.mulVec_zero]

set_option maxHeartbeats 13000000 in
theorem actual_full_rank_minor (A : Matrix U V K) :
    ∃ (r : Fin A.rank ↪ U) (c : Fin A.rank ↪ V),(A.submatrix r c).det≠0 := by
  obtain ⟨c,hc⟩ := spanning_columns A
  let B := A.submatrix id c
  have hRank : Bᵀ.rank=A.rank := (Matrix.rank_transpose B).trans hc
  obtain ⟨row,hrow⟩ := spanning_columns Bᵀ
  let changeRank : Fin A.rank ≃ Fin Bᵀ.rank := finCongr hRank.symm
  let r : Fin A.rank ↪ U := changeRank.toEmbedding.trans row
  let M := A.submatrix r c
  have hM : Mᵀ=(Bᵀ.submatrix id row).submatrix (Equiv.refl _) changeRank := rfl
  have hMRank : M.rank=A.rank := by
    rw [←Matrix.rank_transpose M,hM,Matrix.rank_submatrix,hrow,hRank]
  exact ⟨r,c,square_full_rank_det M (by simpa only [Fintype.card_fin] using hMRank)⟩

#print axioms submatrix_rank_mono
#print axioms spanning_columns
#print axioms square_full_rank_det
#print axioms actual_full_rank_minor
end Paper5.HermiteGeneric
