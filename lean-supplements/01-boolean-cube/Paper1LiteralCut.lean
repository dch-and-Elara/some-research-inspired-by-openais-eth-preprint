import Paper1LiteralPeriod
import BooleanCube.SymmetricAnalysis

/-! Paper 1 §4.2, exact printed cutoff with the *vanishing* margin
`2/log q`. The previously published proof uses a different fixed margin. -/

namespace LocalReconstruction.Paper1Coverage

open Filter
open scoped Topology
noncomputable section

def literalScale (γ : ℝ) (q : ℕ) : ℝ :=
  (2*γ-1)*Real.log q + Real.log (8/Real.pi) + 2/Real.log q

/-- Twice the paper's `x_q`, so the floor below is literally its `ell`. -/
def literalRoot (γ : ℝ) (q : ℕ) : ℝ := Real.sqrt ((q:ℝ)*literalScale γ q)

def literalCut (γ : ℝ) (q : ℕ) : ℕ := ⌊((q:ℝ)-literalRoot γ q)/2⌋₊

def literalGapReal (γ : ℝ) (q : ℕ) : ℝ := (q:ℝ)-2*(literalCut γ q:ℝ)

private theorem q_real_top : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private theorem q_positive : ∀ᶠ q : ℕ in atTop, 0 < (q:ℝ) :=
  q_real_top.eventually_gt_atTop 0

private theorem log_positive : ∀ᶠ q : ℕ in atTop, 0 < Real.log q :=
  symmetric_log_atTop.eventually_gt_atTop 0

private theorem inverse_log_tendsto_zero :
    Tendsto (fun q : ℕ => (Real.log q)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp symmetric_log_atTop

theorem literal_scale_centered (γ : ℝ) :
    Tendsto (fun q : ℕ => literalScale γ q - (2*γ-1)*Real.log q)
      atTop (𝓝 (Real.log (8/Real.pi))) := by
  have h := (inverse_log_tendsto_zero.const_mul (2:ℝ)).const_add (Real.log (8/Real.pi))
  rw [mul_zero, add_zero] at h
  apply h.congr
  intro q
  unfold literalScale
  rw [div_eq_mul_inv]
  ring

theorem literal_scale_log_ratio (γ : ℝ) :
    Tendsto (fun q : ℕ => literalScale γ q / Real.log q) atTop (𝓝 (2*γ-1)) := by
  have h := ((literal_scale_centered γ).mul inverse_log_tendsto_zero).const_add (2*γ-1)
  rw [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [log_positive] with q hl
  field_simp [hl.ne']
  ring

private theorem literal_scale_div_dim (γ : ℝ) :
    Tendsto (fun q : ℕ => literalScale γ q / q) atTop (𝓝 0) := by
  have logdiv := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp q_real_top
  have h := (literal_scale_log_ratio γ).mul logdiv
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [log_positive] with q hl
  change literalScale γ q / Real.log q * (Real.log q / q) = _
  field_simp [hl.ne']

theorem literal_root_sublinear (γ : ℝ) :
    Tendsto (fun q : ℕ => literalRoot γ q / q) atTop (𝓝 0) := by
  have hs := (literal_scale_div_dim γ).sqrt
  rw [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [q_positive] with q hq
  apply (eq_div_iff hq.ne').mpr
  calc
    _ = Real.sqrt ((q:ℝ)^2*(literalScale γ q/q)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq.le, mul_comm]
    _ = literalRoot γ q := by
      unfold literalRoot
      congr 1
      field_simp

/-- The exact printed floor has rounding error in `[0,2)` in full gap units. -/
theorem literal_cut_rounding (γ : ℝ) (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop,
      2*literalCut γ q < q ∧ 0 < literalRoot γ q ∧
      literalRoot γ q ≤ literalGapReal γ q ∧
      literalGapReal γ q < literalRoot γ q+2 ∧
      literalRoot γ q^2 = (q:ℝ)*literalScale γ q := by
  have hp : 0 < 2*γ-1 := by linarith
  have hratio := (literal_scale_log_ratio γ).eventually (Ioi_mem_nhds hp)
  filter_upwards [hratio, log_positive, q_positive,
    (literal_root_sublinear γ).eventually (Iio_mem_nhds zero_lt_one)] with q hr hlog hq small
  have hS : 0 < literalScale γ q := (div_pos_iff_of_pos_right hlog).mp hr
  have hx : 0 < literalRoot γ q := Real.sqrt_pos.mpr (mul_pos hq hS)
  have floorArg : 0 ≤ ((q:ℝ)-literalRoot γ q)/2 := by
    change literalRoot γ q / q < 1 at small
    linarith only [(div_lt_iff₀ hq).mp small]
  have low := Nat.floor_le floorArg
  have high := Nat.lt_floor_add_one (((q:ℝ)-literalRoot γ q)/2)
  have l : literalRoot γ q ≤ literalGapReal γ q := by
    unfold literalGapReal literalCut
    linarith only [low]
  have h : literalGapReal γ q < literalRoot γ q + 2 := by
    unfold literalGapReal literalCut
    linarith only [high]
  have gpos : 0 < literalGapReal γ q := hx.trans_le l
  unfold literalGapReal at gpos
  refine ⟨?_, hx, l, h, Real.sq_sqrt (mul_nonneg hq.le hS.le)⟩
  exact_mod_cast (show 2*(literalCut γ q:ℝ) < q by linarith only [gpos])

theorem literal_gap_in_moderate_window (γ : ℝ) (hγ : 1/2 < γ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ q : ℕ in atTop,
      literalGapReal γ q ≤ M * Real.sqrt ((q:ℝ)*Real.log q) := by
  let C := (2*γ-1)+1
  have hc : 0 < C := by dsimp only [C]; linarith
  refine ⟨Real.sqrt C+2, by positivity, ?_⟩
  have broad := (literal_scale_log_ratio γ).eventually
    (Iio_mem_nhds (show 2*γ-1 < C by dsimp only [C]; linarith))
  have rootTop := Real.tendsto_sqrt_atTop.comp (q_real_top.atTop_mul_atTop₀ symmetric_log_atTop)
  filter_upwards [literal_cut_rounding γ hγ, broad, log_positive, q_positive,
    rootTop.eventually_ge_atTop 1] with q hr hC hL hq hroot
  have hs := (div_lt_iff₀ hL).mp hC
  have hu : literalRoot γ q ≤ Real.sqrt C * Real.sqrt ((q:ℝ)*Real.log q) := by
    rw [← Real.sqrt_mul hc.le]
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_le_mul_of_nonneg_left hs.le hq.le]
  change 1 ≤ Real.sqrt ((q:ℝ)*Real.log q) at hroot
  nlinarith only [hr.2.2.2.1, hu, hroot]

theorem literal_gap_squared_lower (γ : ℝ) (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop, literalScale γ q ≤ literalGapReal γ q^2/q := by
  filter_upwards [literal_cut_rounding γ hγ, q_positive] with q h hq
  have sq := (sq_le_sq₀ h.2.1.le (h.2.1.le.trans h.2.2.1)).mpr h.2.2.1
  apply (le_div_iff₀ hq).mpr
  rw [h.2.2.2.2] at sq
  linarith only [sq]

/-- Rounding the paper's actual cutoff, with no switching to other residues,
preserves the sharp additive constant in its gap scale. -/
theorem literal_gap_constant (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ => literalGapReal γ q^2/q - (2*γ-1)*Real.log q)
      atTop (𝓝 (Real.log (8/Real.pi))) := by
  have invq : Tendsto (fun q : ℕ => 1/(q:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have err : Tendsto (fun q : ℕ => literalGapReal γ q^2/q - literalScale γ q) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun q => 4*(literalRoot γ q/q+1/(q:ℝ))) ?_ ?_
      (by simpa using ((literal_root_sublinear γ).add invq).const_mul 4)
    · exact (literal_gap_squared_lower γ hγ).mono fun _ h => sub_nonneg.mpr h
    · filter_upwards [literal_cut_rounding γ hγ, q_positive] with q h hq
      have hs := (sq_le_sq₀ (h.2.1.le.trans h.2.2.1) (by linarith [h.2.1])).mpr h.2.2.2.1.le
      have he : literalScale γ q = literalRoot γ q^2/q :=
        (eq_div_iff hq.ne').mpr (by linarith only [h.2.2.2.2])
      rw [he, ← sub_div, ← add_div, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hq.le
      nlinarith only [hs]
  have h := err.add (literal_scale_centered γ)
  rw [zero_add] at h
  apply h.congr
  intro q
  dsimp only
  ring

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.literal_scale_centered
#print axioms LocalReconstruction.Paper1Coverage.literal_scale_log_ratio
#print axioms LocalReconstruction.Paper1Coverage.literal_root_sublinear
#print axioms LocalReconstruction.Paper1Coverage.literal_cut_rounding
#print axioms LocalReconstruction.Paper1Coverage.literal_gap_in_moderate_window
#print axioms LocalReconstruction.Paper1Coverage.literal_gap_squared_lower
#print axioms LocalReconstruction.Paper1Coverage.literal_gap_constant
