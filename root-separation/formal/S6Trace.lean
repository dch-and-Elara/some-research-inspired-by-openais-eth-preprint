import BooleanMeasurement
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace

namespace Section6

noncomputable section

abbrev Euc (X : Type*) [Fintype X] := EuclideanSpace ℝ X

variable {X H V : Type*} [Fintype X] [Fintype H] [Fintype V]

lemma euclidean_inner (x y : Euc X) : ⟪x, y⟫ = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

lemma bessel_real {x : V → Euc X} (hx : Orthonormal ℝ x) (y : Euc X) :
    ∑ v, ⟪x v, y⟫ ^ 2 ≤ ‖y‖ ^ 2 := by
  simpa using hx.sum_inner_products_le (s := Finset.univ) y

/-- The trace bound for orthonormal input columns and orthonormal measurement rows.
The column-space dimension here is the dimension *after* measurement. -/
theorem trace_le_measured_dim (row : H → Euc X) (input : V → Euc X)
    (hr : Orthonormal ℝ row) (hi : Orthonormal ℝ input) :
    ∑ v, ∑ h, ⟪row h, input v⟫ ^ 2 ≤
      (Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun v => WithLp.toLp 2 (fun h : H => ⟪row h, input v⟫)))) : ℝ) := by
  classical
  let col (v : V) : Euc H := WithLp.toLp 2 (fun h => ⟪row h, input v⟫)
  let W := Submodule.span ℝ (Set.range col)
  let w (v : V) : W := ⟨col v, Submodule.subset_span ⟨v, rfl⟩⟩
  let b := stdOrthonormalBasis ℝ W
  let lift (z : Euc H) : Euc X := ∑ h, z h • row h
  have hlift (z : Euc H) : ‖lift z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hr.inner_sum, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, pow_two]
  have hcoeff (v : V) (z : W) : ⟪input v, lift z.val⟫ = ⟪w v, z⟫ := by
    change _ = ⟪col v, z.val⟫
    rw [euclidean_inner (col v) z.val]
    change ⟪input v, ∑ h, z.val h • row h⟫ = _
    rw [inner_sum]
    simp [col, real_inner_smul_right, real_inner_comm (input v), mul_comm]
  change (∑ v, ∑ h, ⟪row h, input v⟫ ^ 2) ≤ (Module.finrank ℝ W : ℝ)
  calc
    _ = ∑ v, ‖w v‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      change _ = ‖col v‖ ^ 2
      simp [EuclideanSpace.norm_sq_eq, col, Real.norm_eq_abs, sq_abs]
    _ = ∑ v, ∑ j, ⟪input v, lift (b j).val⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [hcoeff]
      exact (b.sum_sq_inner_left (w v)).symm
    _ = ∑ j, ∑ v, ⟪input v, lift (b j).val⟫ ^ 2 := Finset.sum_comm
    _ ≤ ∑ _ : Fin (Module.finrank ℝ W), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hb : ‖(b j).val‖ = 1 := b.norm_eq_one j
      simpa [hlift, hb] using bessel_real hi (lift (b j).val)
    _ = _ := by simp

/-- Scaling each row and each column after embedding the rational entries into
the reals cannot make the real rank exceed the original rational rank. -/
theorem scaled_real_span_le_rat_rank (C : Matrix H V ℚ) (rowScale : H → ℝ)
    (colScale : V → ℝ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun v =>
      (WithLp.toLp 2 (fun h : H => colScale v * (rowScale h * (C h v : ℝ))) : Euc H)))) ≤
      C.rank := by
  classical
  let f (z : H → ℚ) : Euc H := WithLp.toLp 2 (fun h => rowScale h * (z h : ℝ))
  obtain ⟨s, _, hs, hc⟩ := BooleanMeasurement.exists_independent_columns (K := ℚ) C.col
  let W := Submodule.span ℝ (Set.range (fun v : s => f (C.col v)))
  have hf (z : H → ℚ) (hz : z ∈ Submodule.span ℚ (C.col '' s)) : f z ∈ W := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, rfl⟩ := hz
      exact Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩
    | zero =>
      have he : f 0 = 0 := by ext; simp [f]
      rw [he]
      exact W.zero_mem
    | add a b ha hb ihA ihB =>
      have he : f (a + b) = f a + f b := by ext; simp [f, mul_add]
      rw [he]
      exact W.add_mem ihA ihB
    | smul a b hb ih =>
      have he : f (a • b) = (a : ℝ) • f b := by
        ext
        simp [f, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rw [he]
      exact W.smul_mem _ ih
  have hle : Submodule.span ℝ (Set.range (fun v =>
      (WithLp.toLp 2 (fun h : H => colScale v * (rowScale h * (C h v : ℝ))) : Euc H))) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hv := hf (C.col v) (by rw [hs]; exact Submodule.subset_span ⟨v, rfl⟩)
    exact W.smul_mem (colScale v) hv
  rw [C.rank_eq_finrank_span_cols, ← hc, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Submodule.finrank_mono hle).trans (finrank_range_le_card _)

#print axioms trace_le_measured_dim
#print axioms scaled_real_span_le_rat_rank

end
end Section6



