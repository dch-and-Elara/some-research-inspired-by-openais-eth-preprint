import P5HermiteTransportGenericShift
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Honest lower block triangularity of coefficient-first anchor
multiplication. Its determinant repeats the constant matrix b times. -/
namespace Paper5.HermiteGeneric
open Matrix
open scoped BigOperators Classical

variable {R U : Type*} [CommRing R] [Fintype U] [DecidableEq U]

theorem convolution_det {b : ℕ} (hb : 0<b) (C : Fin b→Matrix U U R) :
    (convolution C).det = (C ⟨0,hb⟩).det^b := by
  let f : Fin b × U → (Fin b)ᵒᵈ := fun x=>OrderDual.toDual x.1
  let B := convolution C
  have hB : B.BlockTriangular f := by
    rintro ⟨r,u⟩ ⟨l,v⟩ h
    have hx : r.val<l.val := h
    change convolution C (r,u) (l,v)=0
    rw [convolution_apply,dif_neg (not_le_of_gt hx)]
  calc
    _ = ∏ t : (Fin b)ᵒᵈ,(B.toSquareBlock f t).det := hB.det_fintype
    _ = ∏ _t : (Fin b)ᵒᵈ,(C ⟨0,hb⟩).det := by
      apply Finset.prod_congr rfl
      intro t _
      let e : U ≃ {x : Fin b × U // f x=t} :=
        { toFun := fun u=>⟨(OrderDual.ofDual t,u),rfl⟩
          invFun := fun x=>x.val.2
          left_inv := fun _=>rfl
          right_inv := fun x=>Subtype.ext (Prod.ext (congrArg OrderDual.ofDual x.property).symm rfl) }
      have h : (B.toSquareBlock f t).submatrix e e=C ⟨0,hb⟩ := by
        ext u v
        change convolution C (OrderDual.ofDual t,u) (OrderDual.ofDual t,v)=C ⟨0,hb⟩ u v
        rw [convolution_apply,dif_pos le_rfl]
        congr 2
        exact Nat.sub_self _
      have hed := Matrix.det_submatrix_equiv_self e (B.toSquareBlock f t)
      rw [h] at hed
      exact hed.symm
    _ = _ := by simp

variable {K : Type*} [Field K]

theorem convolution_rank {b : ℕ} (hb : 0<b) (C : Fin b→Matrix U U K)
    (h : (C ⟨0,hb⟩).det≠0) :
    (convolution C).rank=b*Fintype.card U := by
  have hu : IsUnit (convolution C).det := by
    rw [convolution_det hb]
    exact (isUnit_iff_ne_zero.mpr h).pow b
  have hRank := Matrix.rank_of_isUnit (convolution C) ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  simpa only [Fintype.card_prod,Fintype.card_fin] using hRank

#print axioms convolution_det
#print axioms convolution_rank
end Paper5.HermiteGeneric
