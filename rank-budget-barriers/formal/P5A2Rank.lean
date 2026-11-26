import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact rank of a one-variable Hankel form cut off at the truncation
boundary. No determinants of the entire singular matrix are used. -/
namespace P5A2
open Matrix
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem rank_submatrix_le {I J U V : Type*} [Fintype I] [Fintype J] [Fintype U] [Fintype V]
    (M : Matrix I J K) (a : U → I) (b : V → J) :
    (M.submatrix a b).rank ≤ M.rank := by
  let A := M.submatrix a id
  have hA : A.rank ≤ M.rank := Matrix.rank_submatrix_le a (Equiv.refl J) M
  have hB : (Aᵀ.submatrix b id).rank ≤ Aᵀ.rank :=
    Matrix.rank_submatrix_le b (Equiv.refl U) Aᵀ
  have he : (Aᵀ.submatrix b id)ᵀ = M.submatrix a b := rfl
  calc
    _ = (Aᵀ.submatrix b id).rank := (congrArg Matrix.rank he.symm).trans (Matrix.rank_transpose _)
    _ ≤ Aᵀ.rank := hB
    _ = A.rank := Matrix.rank_transpose A
    _ ≤ _ := hA

/-- Rank upper bound from a literal zero-row prefix support. -/
theorem rank_prefix {k d : ℕ} (M : Matrix (Fin k) (Fin k) K)
    (hd : d ≤ k) (hz : ∀ i j, d ≤ i.val → M i j = 0) : M.rank ≤ d := by
  let U : Matrix (Fin k) (Fin d) K := Matrix.of fun i v => if i.val=v.val then 1 else 0
  let V : Matrix (Fin d) (Fin k) K := M.submatrix (Fin.castLE hd) id
  have he : U*V = M := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    by_cases h : i.val<d
    · rw [Finset.sum_eq_single (⟨i.val,h⟩ : Fin d)]
      · have hcast : Fin.castLE hd (⟨i.val,h⟩ : Fin d) = i := Fin.ext rfl
        simp [U,V,hcast]
      · intro u _ hu
        have hn : i.val ≠ u.val := fun hh => hu (Fin.ext hh.symm)
        simp [U,hn]
      · simp
    · rw [hz i j (Nat.le_of_not_gt h)]
      apply Finset.sum_eq_zero
      intro u _
      have hn : i.val ≠ u.val := fun hh => h (hh.symm ▸ u.isLt)
      simp [U,hn]
  rw [←he]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width U)

/-- Top cutoff is encoded before ranking, even if the sequence λ outside
the declared jet range happens to have nonzero entries. -/
def hankel (k : ℕ) (f : ℕ → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => if i.val+j.val<k then f (i.val+j.val) else 0

set_option maxHeartbeats 4300000 in
theorem hankel_rank_of_last {k : ℕ} (f : ℕ → K) (r : Fin k)
    (hn : f r.val ≠ 0) (ht : ∀ j, r.val < j → j < k → f j = 0) :
    (hankel k f).rank = r.val+1 := by
  have hcap : r.val+1 ≤ k := Nat.succ_le_of_lt r.isLt
  apply le_antisymm
  · refine rank_prefix (hankel k f) hcap (fun i j hi => ?_)
    change (if i.val+j.val<k then f (i.val+j.val) else 0) = 0
    split
    · rename_i h
      exact ht _ (by omega) h
    · rfl
  · let d := r.val+1
    let row : Fin d → Fin k := Fin.castLE hcap
    let col (i : Fin d) : Fin k := ⟨r.val-i.val,by omega⟩
    let A := (hankel k f).submatrix row col
    have htA : A.BlockTriangular id := by
      intro i j hij
      change j.val < i.val at hij
      change (if i.val+(r.val-j.val)<k then f (i.val+(r.val-j.val)) else 0) = 0
      split
      · rename_i h
        exact ht _ (by have hj := j.isLt; dsimp [d] at hj; omega) h
      · rfl
    have hdA (i : Fin d) : A i i = f r.val := by
      have he : i.val+(r.val-i.val)=r.val := by have hh := i.isLt; dsimp[d] at hh; omega
      change (if i.val+(r.val-i.val)<k then f (i.val+(r.val-i.val)) else 0) = _
      rw [he,if_pos r.isLt]
    have hm : A.det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htA]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdA i ▸ hn)
    obtain ⟨u,hu⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr hm.isUnit
    have hr₀ : A.rank = Fintype.card (Fin d) := hu ▸ Matrix.rank_unit u
    have hr : A.rank = r.val+1 := by simpa [d] using hr₀
    exact hr.symm.le.trans (rank_submatrix_le (hankel k f) row col)

theorem hankel_rank_zero {k : ℕ} (f : ℕ → K) (h : ∀ j < k, f j = 0) :
    (hankel k f).rank = 0 := by
  have hz : hankel k f = 0 := by
    apply Matrix.ext
    intro i j
    change (if i.val+j.val<k then f (i.val+j.val) else 0) = _
    split
    · rename_i hi
      exact h _ hi
    · rfl
  rw [hz,Matrix.rank_zero]

#print axioms rank_submatrix_le
#print axioms rank_prefix
#print axioms hankel_rank_of_last
#print axioms hankel_rank_zero
end P5A2
