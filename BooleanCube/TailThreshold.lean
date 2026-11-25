import BooleanCube.Moderate

namespace LocalReconstruction
open Filter Real
open scoped Topology
noncomputable section

/-- The lower endpoint in (5), prior to adding its vanishing error. -/
def asymmetricLowerEndpoint (γ : ℝ) (q : ℕ) : ℝ :=
  (2*γ-1)*Real.log q - 2*Real.log (Real.log q) +
    Real.log (2/(Real.pi*(2*γ-1)^2))

private theorem natCast_top : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

theorem cube_log_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp natCast_top

theorem cube_log_div_nat : Tendsto (fun q : ℕ => Real.log q/q) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp natCast_top

theorem asymmetric_endpoint_ratio (γ ε : ℝ) :
    Tendsto (fun q : ℕ => (asymmetricLowerEndpoint γ q - ε) / Real.log q)
      atTop (𝓝 (2*γ-1)) := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp cube_log_atTop
  have hconst := (tendsto_inv_atTop_zero.comp cube_log_atTop).const_mul
    (Real.log (2/(Real.pi*(2*γ-1)^2)) - ε)
  have h := ((tendsto_const_nhds (x := (2*γ-1))).sub (hl.const_mul 2)).add hconst
  rw [mul_zero, mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [cube_log_atTop.eventually_gt_atTop 0] with q hq
  dsimp [asymmetricLowerEndpoint, Function.comp_def]
  field_simp
  ring

/-- The squared gap divided by dimension, used in the weighted tail estimate. -/
def scaledGap (q k : ℕ) : ℝ := binomialGap q k ^ 2 / q

/-- Tail density divided by the allowable measurement density q⁻ᵞ. -/
def budgetTail (q k : ℕ) (γ : ℝ) : ℝ :=
  weightedTail q k / (((k : ℝ)+1)*(2:ℝ)^q) * (q:ℝ)^γ

private def tailQuotient (q k : ℕ) : ℝ :=
  weightedTail q k / (((k : ℝ)+1)*(2:ℝ)^q) *
    (Real.sqrt (2*Real.pi*q) * scaledGap q k * Real.exp (scaledGap q k / 2))

private theorem tailQuotient_limit {k : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hg : ∀ᶠ q : ℕ in atTop, 0 ≤ binomialGap q (k q))
    (h : Tendsto (fun q : ℕ => scaledGap q (k q) / Real.log q) atTop (𝓝 c)) :
    Tendsto (fun q => tailQuotient q (k q)) atTop (𝓝 1) := by
  have lower := h.eventually (Ioi_mem_nhds (show c/2 < c by linarith))
  have upper := h.eventually (Iio_mem_nhds (show c < 2*c by linarith))
  have hw : ∀ᶠ q : ℕ in atTop, Real.sqrt (c/2) * Real.sqrt ((q:ℝ)*Real.log q) ≤ binomialGap q (k q) ∧ Real.sqrt (2*c) * Real.sqrt ((q:ℝ)*Real.log q) ≥ binomialGap q (k q) := by
    filter_upwards [lower, upper, hg, cube_log_atTop.eventually_gt_atTop 0,
        natCast_top.eventually_gt_atTop 0] with q hlo hup hg hl hq
    change c/2 < scaledGap q (k q)/Real.log q at hlo
    change scaledGap q (k q)/Real.log q < 2*c at hup
    have lo := (lt_div_iff₀ hl).mp hlo
    have up := (div_lt_iff₀ hl).mp hup
    unfold scaledGap at lo up
    have lo' := (lt_div_iff₀ hq).mp lo
    have up' := (div_lt_iff₀ hq).mp up
    constructor
    · apply le_of_sq_le_sq _ hg
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith only [lo']
    · apply le_of_sq_le_sq _ (by positivity)
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith only [up']
  apply (weighted_binomial_asymptotic k _ _ (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity)) hw).congr
  intro q
  simp only [tailQuotient, scaledGap, div_div]
  ring_nf

private theorem threshold_exponential {γ : ℝ} (hγ : 1/2 < γ) (ε : ℝ)
    {q : ℕ} (hq : 0 < (q:ℝ)) (hlog : 0 < Real.log q) :
    (q:ℝ)^γ = Real.sqrt (2*Real.pi*q) * ((2*γ-1)*Real.log q) *
      Real.exp ((asymmetricLowerEndpoint γ q - ε)/2) * Real.exp (ε/2) / 2 := by
  let c : ℝ := 2*γ-1
  let a : ℝ := 2 / (Real.sqrt (2*Real.pi) * c)
  have hc : 0 < c := by dsimp [c]; linarith
  have hs : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have ha : 0 < a := by dsimp [a]; positivity
  have hasq : a^2 = 2/(Real.pi*c^2) := by
    dsimp [a]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [Real.pi_ne_zero, hc.ne']
  have hsplit : (asymmetricLowerEndpoint γ q - ε)/2 =
      (γ-1/2)*Real.log q - Real.log (Real.log q) + Real.log a - ε/2 := by
    unfold asymmetricLowerEndpoint
    change (c*Real.log q - 2*Real.log (Real.log q) + Real.log (2/(Real.pi*c^2))-ε)/2 = _
    rw [← hasq, Real.log_pow]
    ring
  rw [hsplit, Real.exp_sub, Real.exp_add, Real.exp_sub, Real.exp_log hlog,
    Real.exp_log ha, Real.sqrt_mul (show 0 ≤ 2*Real.pi by positivity),
    Real.sqrt_eq_rpow (q:ℝ), mul_comm (γ-1/2) (Real.log q), ← Real.rpow_def_of_pos hq]
  have hp : (q:ℝ)^(1/2:ℝ) * (q:ℝ)^(γ-1/2) = (q:ℝ)^γ := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  change _ = (Real.sqrt (2*Real.pi) * (q:ℝ)^(1/2:ℝ)) * (c * Real.log q) * _ * _ / _
  rw [← hp]
  dsimp [a]
  field_simp [hs.ne', hc.ne', hlog.ne', (Real.exp_pos (ε/2)).ne']

/-- Invert the moderate-tail estimate at a fixed offset from the endpoint in (5).
A large positive gap error makes the corresponding exponential factor vanish. -/
theorem budgetTail_limit {γ ε b : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hg : ∀ᶠ q : ℕ in atTop, 0 ≤ binomialGap q (k q))
    (hs : Tendsto (fun q => scaledGap q (k q) / Real.log q) atTop (𝓝 (2*γ-1)))
    (he : Tendsto (fun q => Real.exp ((asymmetricLowerEndpoint γ q - ε -
      scaledGap q (k q))/2)) atTop (𝓝 b)) :
    Tendsto (fun q => budgetTail q (k q) γ) atTop (𝓝 (b * Real.exp (ε/2) / 2)) := by
  have hc : 0 < 2*γ-1 := by linarith
  have ht := tailQuotient_limit hc hg hs
  have hr := (tendsto_const_nhds (x := (2*γ-1))).div hs hc.ne'
  rw [div_self hc.ne'] at hr
  have h := (((ht.mul hr).mul he).mul_const (Real.exp (ε/2))).div_const 2
  rw [one_mul, one_mul] at h
  apply h.congr'
  filter_upwards [cube_log_atTop.eventually_gt_atTop 0,
    natCast_top.eventually_gt_atTop 0, hs.eventually (Ioi_mem_nhds hc)] with q hl hq hp
  change 0 < scaledGap q (k q) / Real.log q at hp
  have hspos : 0 < scaledGap q (k q) := by simpa using (lt_div_iff₀ hl).mp hp
  have hExp := threshold_exponential hγ ε hq hl
  simp only [tailQuotient, budgetTail, Pi.div_apply]
  rw [hExp, show (asymmetricLowerEndpoint γ q - ε - scaledGap q (k q))/2 =
    (asymmetricLowerEndpoint γ q - ε)/2 - scaledGap q (k q)/2 by ring, Real.exp_sub]
  field_simp [hl.ne', hspos.ne', (Real.exp_pos (scaledGap q (k q)/2)).ne']

end
end LocalReconstruction

