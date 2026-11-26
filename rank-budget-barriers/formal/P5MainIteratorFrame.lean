import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Bessel/Parseval step in F.A1. It uses the measured rank (not the
number of auxiliary rows) and two actual orthonormal families. -/
namespace P5MainIterator
open Matrix Module
open scoped BigOperators RealInnerProductSpace Classical

variable {E H V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype H] [Fintype V]

noncomputable def assemble (c : H → E) : (H → ℝ) →ₗ[ℝ] E where
  toFun a := ∑ h, a h • c h
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum,smul_smul]

theorem coordinate_assemble (c : H → E) (hc : Orthonormal ℝ c)
    (l : H → ℝ) (h : H) :
    ⟪c h,assemble c l⟫ = l h := by
  exact hc.inner_right_fintype l h

theorem assemble_inner (c : H → E) (hc : Orthonormal ℝ c)
    (l u : H → ℝ) :
    ⟪assemble c l, assemble c u⟫ = ∑ h, l h * u h := by
  change ⟪(∑ h, l h • c h), assemble c u⟫ = _
  simp only [sum_inner,real_inner_smul_left,coordinate_assemble c hc]

set_option maxHeartbeats 4600000 in
/-- Form the restricted actual measurement matrix. The column energy is
at most its rank, even when there are far more available auxiliary rows. -/
theorem orthonormal_frame_rank [FiniteDimensional ℝ E]
    (c : H → E) (w : V → E)
    (hc : Orthonormal ℝ c) (hw : Orthonormal ℝ w) :
    (∑ v, ∑ h, ⟪c h,w v⟫ ^ 2) ≤
      ((Matrix.of fun h v => ⟪c h,w v⟫).rank : ℝ) := by
  let M : Matrix H V ℝ := Matrix.of fun h v => ⟪c h,w v⟫
  let S : Submodule ℝ E := (Submodule.span ℝ (Set.range M.col)).map (assemble c)
  let P (v : V) : S :=
    ⟨assemble c (M.col v),Submodule.mem_map_of_mem (Submodule.subset_span ⟨v,rfl⟩)⟩
  have hi (x : S) (v : V) : ⟪x,P v⟫ = ⟪(x:E),w v⟫ := by
    obtain ⟨l,_,hl⟩ := x.property
    change ⟪(x:E),assemble c (M.col v)⟫ = _
    rw [←hl,assemble_inner c hc]
    change _ = ⟪(∑ h,l h • c h),w v⟫
    simp only [sum_inner,real_inner_smul_left]
    rfl
  have hnorm (v : V) : (∑ h, ⟪c h,w v⟫ ^ 2) = ‖P v‖^2 := by
    change (∑ h, (M.col v h)^2) = ‖assemble c (M.col v)‖^2
    rw [← real_inner_self_eq_norm_sq,assemble_inner c hc]
    simp only [pow_two]
  let b := stdOrthonormalBasis ℝ S
  have hbound (i : Fin (Module.finrank ℝ S)) : (∑ v, ⟪b i,P v⟫^2) ≤ 1 := by
    have hx := hw.sum_inner_products_le (s:=Finset.univ) ((b i : S) : E)
    rw [show ‖((b i : S) : E)‖=1 from b.orthonormal.norm_eq_one i,one_pow] at hx
    calc
      _ = ∑ v, ‖⟪w v,((b i : S):E)⟫‖^2 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hi,real_inner_comm ((b i : S):E) (w v),Real.norm_eq_abs,sq_abs]
      _ ≤ _ := hx
  change (∑ v, ∑ h, (M.col v h)^2) ≤ (M.rank:ℝ)
  calc
    _ = ∑ v, ‖P v‖^2 := Finset.sum_congr rfl (fun v _ => hnorm v)
    _ = ∑ v, ∑ i, ⟪b i,P v⟫^2 :=
      Finset.sum_congr rfl (fun v _ => (b.sum_sq_inner_right (P v)).symm)
    _ = ∑ i, ∑ v, ⟪b i,P v⟫^2 := Finset.sum_comm
    _ ≤ ∑ _i : Fin (Module.finrank ℝ S), (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = (Module.finrank ℝ S : ℝ) := by simp
    _ ≤ _ := by
      exact_mod_cast (show Module.finrank ℝ S ≤ M.rank from by
        rw [Matrix.rank_eq_finrank_span_cols]
        exact Submodule.finrank_map_le _ _)

#print axioms coordinate_assemble
#print axioms assemble_inner
#print axioms orthonormal_frame_rank
end P5MainIterator
