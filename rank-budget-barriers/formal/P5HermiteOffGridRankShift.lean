import P5HermiteTransportGenericMinors

/-! The shift already used by the actual H.1 transport has exactly k-j
live columns, verified by its literal one-hot factors and identity minor. -/
namespace Paper5.HermiteOffGrid
open Paper5.HermiteGeneric Matrix
open scoped BigOperators Classical

variable {K : Type*} [Field K]

set_option maxHeartbeats 13000000 in
theorem truncated_shift_rank (k : ℕ) (j : Fin k) :
    (shiftMatrix K k j.val).rank=k-j.val := by
  let Z := shiftMatrix K k j.val
  let d := k-j.val
  let A : Matrix (Fin k) (Fin d) K := Matrix.of fun r i=>if r.val=i.val+j.val then 1 else 0
  let B : Matrix (Fin d) (Fin k) K := Matrix.of fun i l=>if i.val=l.val then 1 else 0
  have hZ : A*B=Z := by
    ext r l
    rw [Matrix.mul_apply]
    by_cases h : l.val<d
    · let i : Fin d := ⟨l.val,h⟩
      rw [Finset.sum_eq_single i]
      · exact (show A r i*B i l=Z r l by simp [A,B,Z,i])
      · intro a _ hne
        have hv : a.val≠l.val := fun h'=>hne (Fin.ext h')
        simp [B,hv]
      · simp
    · have rhs : Z r l=0 := by
        have hrl : r.val≠l.val+j.val := by
          have hr:=r.isLt
          dsimp [d] at h
          omega
        simp [Z,hrl]
      rw [rhs]
      apply Finset.sum_eq_zero
      intro i _
      have hv : i.val≠l.val := fun he=>h (he ▸ i.isLt)
      simp [B,hv]
  let row (i : Fin d) : Fin k := ⟨i.val+j.val,by
    have hi:=i.isLt
    dsimp [d] at hi
    omega⟩
  let col (i : Fin d) : Fin k := ⟨i.val,by have hi:=i.isLt; dsimp [d] at hi; omega⟩
  have hI : Z.submatrix row col=1 := by
    ext i l
    have he : (row i).val=(col l).val+j.val ↔ i=l := by
      change i.val+j.val=l.val+j.val ↔ i=l
      constructor
      · intro h
        exact Fin.ext (Nat.add_right_cancel h)
      · rintro rfl
        rfl
    simp only [Z,Matrix.submatrix_apply,shiftMatrix_apply,he,Matrix.one_apply]
  change Z.rank=d
  apply le_antisymm
  · rw [←hZ]
    exact (Matrix.rank_mul_le_left A B).trans (by simpa only [Fintype.card_fin] using A.rank_le_card_width)
  · have h := submatrix_rank_mono Z row col
    rw [hI,Matrix.rank_one,Fintype.card_fin] at h
    exact h

#print axioms truncated_shift_rank
end Paper5.HermiteOffGrid
