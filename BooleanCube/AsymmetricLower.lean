import BooleanCube.TailThreshold
import BooleanCube.TailReflection

namespace LocalReconstruction
open Filter Real
open scoped Topology
noncomputable section

private theorem dim_top : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private theorem eventually_dim_pos : ∀ᶠ q : ℕ in atTop, 0 < (q:ℝ) :=
  dim_top.eventually_gt_atTop 0

private theorem eventually_log_pos : ∀ᶠ q : ℕ in atTop, 0 < Real.log q :=
  cube_log_atTop.eventually_gt_atTop 0

private def threshold (γ ε : ℝ) (q : ℕ) : ℝ :=
  asymmetricLowerEndpoint γ q - ε

private def thresholdRoot (γ ε : ℝ) (q : ℕ) : ℝ :=
  Real.sqrt ((q:ℝ)*threshold γ ε q)

private def thresholdIndex (γ ε : ℝ) (q : ℕ) : ℕ :=
  (q - ⌊thresholdRoot γ ε q⌋₊ - 1)/2

private def reflectLength (q : ℕ) : ℕ := ⌊Real.sqrt q⌋₊

private theorem threshold_top {γ : ℝ} (hγ : 1/2 < γ) (ε : ℝ) :
    Tendsto (threshold γ ε) atTop atTop := by
  have hc : 0 < (2*γ-1)/2 := by linarith
  apply tendsto_atTop_mono' atTop _ (cube_log_atTop.const_mul_atTop hc)
  filter_upwards [eventually_log_pos,
    (asymmetric_endpoint_ratio γ ε).eventually
      (Ioi_mem_nhds (show (2*γ-1)/2 < 2*γ-1 by linarith))] with q hl h
  exact ((lt_div_iff₀ hl).mp h).le

private theorem thresholdRoot_div_dim (γ ε : ℝ) :
    Tendsto (fun q => thresholdRoot γ ε q / q) atTop (𝓝 0) := by
  have h := (asymmetric_endpoint_ratio γ ε).mul cube_log_div_nat
  rw [mul_zero] at h
  have ht : Tendsto (fun q => threshold γ ε q / q) atTop (𝓝 0) := by
    apply h.congr'
    filter_upwards [eventually_log_pos] with q hl
    change threshold γ ε q / Real.log q * (Real.log q / q) = _
    field_simp [hl.ne']
  have hs := (Real.continuous_sqrt.tendsto 0).comp ht
  rw [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_dim_pos] with q hq
  change Real.sqrt (threshold γ ε q/q) = thresholdRoot γ ε q/q
  have e : (q:ℝ)*threshold γ ε q = (q:ℝ)^2*(threshold γ ε q/q) := by field_simp
  rw [thresholdRoot, e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq.le]
  field_simp

private theorem sqrt_dim_div_dim :
    Tendsto (fun q : ℕ => Real.sqrt q/q) atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_inv_atTop_zero.comp dim_top)
  rw [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_dim_pos] with q hq
  change Real.sqrt ((q:ℝ)⁻¹) = Real.sqrt q/q
  have hp := Real.sqrt_pos.mpr hq
  rw [Real.sqrt_inv]
  field_simp
  exact (Real.sq_sqrt hq.le).symm

private theorem reflectLength_ratio :
    Tendsto (fun q : ℕ => (reflectLength q:ℝ)/q) atTop (𝓝 0) :=
  squeeze_zero (fun _ => by positivity)
    (fun _ => div_le_div_of_nonneg_right (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _))
    sqrt_dim_div_dim

private theorem cutoff_data (γ ε : ℝ) :
    ∀ᶠ q : ℕ in atTop, let k := thresholdIndex γ ε q
      let L := reflectLength q
      ⌊thresholdRoot γ ε q⌋₊ + 2*k < q ∧ L < k ∧
      thresholdRoot γ ε q < binomialGap q k ∧
      binomialGap q k ≤ thresholdRoot γ ε q + 2 := by
  filter_upwards [eventually_ge_atTop 16,
    (thresholdRoot_div_dim γ ε).eventually (Iio_mem_nhds (show (0:ℝ) < 1/4 by norm_num)),
    reflectLength_ratio.eventually (Iio_mem_nhds (show (0:ℝ) < 1/4 by norm_num))]
    with q hq hroot hL
  dsimp only
  have qp : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  let D := ⌊thresholdRoot γ ε q⌋₊
  let k := thresholdIndex γ ε q
  have hD : 4*D < q := by
    have hb := Nat.floor_le (Real.sqrt_nonneg ((q:ℝ)*threshold γ ε q))
    change (D:ℝ) ≤ thresholdRoot γ ε q at hb
    have he := (div_lt_iff₀ qp).mp hroot
    exact_mod_cast (show 4*(D:ℝ) < q by linarith)
  have hLn : 4*reflectLength q < q := by
    have he := (div_lt_iff₀ qp).mp hL
    exact_mod_cast (show 4*(reflectLength q:ℝ) < q by linarith)
  have hk : k = (q-D-1)/2 := rfl
  have lo : D + 2*k + 1 ≤ q := by omega
  have hi : q ≤ D + 2*k + 2 := by omega
  have hcasts : (D:ℝ)+2*(k:ℝ)+1 ≤ q ∧ (q:ℝ) ≤ (D:ℝ)+2*(k:ℝ)+2 := by
    exact ⟨by exact_mod_cast lo, by exact_mod_cast hi⟩
  have fd := Nat.floor_le (Real.sqrt_nonneg ((q:ℝ)*threshold γ ε q))
  have fu := Nat.lt_floor_add_one (thresholdRoot γ ε q)
  change _ + 2*k < q ∧ reflectLength q < k ∧ _ < binomialGap q k ∧ _
  refine ⟨by change D + 2*k < q; omega, by omega, ?_, ?_⟩
  · unfold binomialGap
    linarith [hcasts.1]
  · unfold binomialGap
    change (D:ℝ) ≤ thresholdRoot γ ε q at fd
    linarith [hcasts.2]

private theorem scaledGap_threshold_ratio {γ ε : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 10*Real.sqrt q) :
    Tendsto (fun q => scaledGap q (k q)/Real.log q) atTop (𝓝 (2*γ-1)) := by
  have hr := asymmetric_endpoint_ratio γ ε
  have hs := (Real.continuous_sqrt.tendsto (2*γ-1)).comp hr
  have hi := (Real.continuous_sqrt.tendsto 0).comp (tendsto_inv_atTop_zero.comp cube_log_atTop)
  rw [Real.sqrt_zero] at hi
  have he := hs.add (hi.const_mul 10)
  rw [mul_zero, add_zero] at he
  have ht : Tendsto (fun q : ℕ =>
      binomialGap q (k q) / (Real.sqrt q * Real.sqrt (Real.log q)))
      atTop (𝓝 (Real.sqrt (2*γ-1))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs he
    all_goals
      filter_upwards [hb,eventually_dim_pos,eventually_log_pos,
        (threshold_top hγ ε).eventually_ge_atTop 0] with q b hq hl hT
      have sq := Real.sqrt_pos.mpr hq
      have sl := Real.sqrt_pos.mpr hl
      have hR : thresholdRoot γ ε q = Real.sqrt q * Real.sqrt (threshold γ ε q) :=
        Real.sqrt_mul hq.le _
      have hdiv : Real.sqrt (threshold γ ε q/Real.log q) =
          Real.sqrt (threshold γ ε q) / Real.sqrt (Real.log q) :=
        Real.sqrt_div hT _
      change 0 ≤ threshold γ ε q at hT
    · change Real.sqrt (threshold γ ε q/Real.log q) ≤ _
      rw [hdiv]
      rw [hR] at b
      apply (le_div_iff₀ (mul_pos sq sl)).mpr
      field_simp
      nlinarith only [b.1]
    · change _ ≤ Real.sqrt (threshold γ ε q/Real.log q) + 10*Real.sqrt ((Real.log q)⁻¹)
      rw [hdiv, Real.sqrt_inv]
      apply (div_le_iff₀ (mul_pos sq sl)).mpr
      rw [hR] at b
      field_simp
      nlinarith only [b.2]
  have ht2 := ht.pow 2
  rw [Real.sq_sqrt (by linarith)] at ht2
  apply ht2.congr
  intro q
  simp only [scaledGap, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q),
    Real.sq_sqrt (Real.log_natCast_nonneg q), div_div]

private theorem scaledGap_near_threshold {γ ε : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 4) :
    Tendsto (fun q => scaledGap q (k q) - threshold γ ε q) atTop (𝓝 0) := by
  have h := ((thresholdRoot_div_dim γ ε).const_mul 8).add
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul 16)
  rw [mul_zero, mul_zero, add_zero] at h
  apply squeeze_zero' ?_ ?_ h
  all_goals
    filter_upwards [hb,eventually_dim_pos,(threshold_top hγ ε).eventually_ge_atTop 0]
      with q b hq hT
    have hs := Real.sq_sqrt (mul_nonneg hq.le hT)
    change thresholdRoot γ ε q ^ 2 = _ at hs
    have hR : 0 ≤ thresholdRoot γ ε q := Real.sqrt_nonneg _
  · change 0 ≤ scaledGap q (k q) - threshold γ ε q
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hq).mpr
    nlinarith only [hs, (sq_le_sq₀ hR (hR.trans b.1)).mpr b.1]
  · change scaledGap q (k q) - threshold γ ε q ≤
        8*(thresholdRoot γ ε q/q) + 16*(1/q)
    unfold scaledGap
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    rw [sub_le_iff_le_add]
    have e : (8*thresholdRoot γ ε q+16*1)/(q:ℝ) + threshold γ ε q =
        (8*thresholdRoot γ ε q+16+q*threshold γ ε q)/q := by field_simp
    rw [e]
    apply (div_le_div_iff_of_pos_right hq).mpr
    nlinarith only [hs,(sq_le_sq₀ (hR.trans b.1) (by positivity)).mpr b.2]

private theorem scaledGap_far_threshold {γ ε : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop,
      thresholdRoot γ ε q + Real.sqrt q ≤ binomialGap q (k q)) :
    Tendsto (fun q => scaledGap q (k q) - threshold γ ε q) atTop atTop := by
  have ht := (Real.tendsto_sqrt_atTop.comp (threshold_top hγ ε)).const_mul_atTop
    (show (0:ℝ) < 2 by norm_num)
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [hb,eventually_dim_pos,(threshold_top hγ ε).eventually_ge_atTop 0]
    with q b hq hT
  change 2*Real.sqrt (threshold γ ε q) ≤ scaledGap q (k q) - threshold γ ε q
  unfold scaledGap
  rw [le_sub_iff_add_le]
  apply (le_div_iff₀ hq).mpr
  change Real.sqrt ((q:ℝ)*threshold γ ε q) + Real.sqrt q ≤ _ at b
  rw [Real.sqrt_mul hq.le] at b
  have h := (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤
    Real.sqrt q * Real.sqrt (threshold γ ε q) + Real.sqrt q).trans b)).mpr b
  have e : Real.sqrt q * Real.sqrt (threshold γ ε q) + Real.sqrt q =
      Real.sqrt q * (Real.sqrt (threshold γ ε q)+1) := by ring
  rw [e, mul_pow, Real.sq_sqrt hq.le] at h
  nlinarith only [h, Real.sq_sqrt hT, congrArg (fun x : ℝ => (q:ℝ)*x) (Real.sq_sqrt hT)]


private theorem cutoff_gap_data (γ ε : ℝ) :
    ∀ᶠ q : ℕ in atTop, let R := thresholdRoot γ ε q
      let k := thresholdIndex γ ε q
      let L := reflectLength q
      (R ≤ binomialGap q k ∧ binomialGap q k ≤ R + 4) ∧
      (R ≤ binomialGap q (k-1) ∧ binomialGap q (k-1) ≤ R + 4) ∧
      (R + Real.sqrt q ≤ binomialGap q (k-L-1) ∧
        binomialGap q (k-L-1) ≤ R + 10*Real.sqrt q) := by
  filter_upwards [cutoff_data γ ε, dim_top.eventually_ge_atTop 1] with q h hq
  let R := thresholdRoot γ ε q
  let k := thresholdIndex γ ε q
  let L := reflectLength q
  change _ ∧ L < k ∧ R < binomialGap q k ∧ binomialGap q k ≤ R+2 at h
  have e1 : binomialGap q (k-1) = binomialGap q k + 2 := by
    unfold binomialGap
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
    ring
  have eL : binomialGap q (k-L-1) = binomialGap q k + 2*(L:ℝ)+2 := by
    unfold binomialGap
    rw [Nat.cast_sub (show 1 ≤ k-L by omega), Nat.cast_sub h.2.1.le, Nat.cast_one]
    ring
  have hl := Nat.floor_le (Real.sqrt_nonneg (q:ℝ))
  have hu := Nat.lt_floor_add_one (Real.sqrt (q:ℝ))
  have hs : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  change (R ≤ binomialGap q k ∧ binomialGap q k ≤ R+4) ∧
    (R ≤ binomialGap q (k-1) ∧ binomialGap q (k-1) ≤ R+4) ∧
    (R+Real.sqrt q ≤ binomialGap q (k-L-1) ∧ binomialGap q (k-L-1) ≤ R+10*Real.sqrt q)
  change (L:ℝ) ≤ Real.sqrt q at hl
  change Real.sqrt q < (L:ℝ)+1 at hu
  rw [e1, eL]
  exact ⟨⟨h.2.2.1.le, by linarith [h.2.2.2]⟩,
    ⟨by linarith [h.2.2.1], by linarith [h.2.2.2]⟩,
    ⟨by linarith [h.2.2.1, hu], by linarith [h.2.2.2, hl]⟩⟩

private theorem broad_of_near {γ ε : ℝ} {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 4) :
    ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 10*Real.sqrt q := by
  filter_upwards [hb, dim_top.eventually_ge_atTop 1] with q b hq
  have hs : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  exact ⟨b.1, by linarith [b.2]⟩

private theorem cutoff_index_ratio {γ ε : ℝ} {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 10*Real.sqrt q) :
    Tendsto (fun q : ℕ => ((k q:ℝ)+1)/q) atTop (𝓝 (1/2)) := by
  have h := (thresholdRoot_div_dim γ ε).add (sqrt_dim_div_dim.const_mul 10)
  rw [mul_zero, add_zero] at h
  have hg : Tendsto (fun q : ℕ => binomialGap q (k q)/q) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ h
    all_goals filter_upwards [hb, eventually_dim_pos] with q b hq
    · exact div_nonneg ((Real.sqrt_nonneg _).trans b.1) hq.le
    · rw [← mul_div_assoc, ← add_div]
      exact div_le_div_of_nonneg_right b.2 hq.le
  have hi := ((tendsto_const_nhds (x := (1:ℝ))).sub hg).div_const 2
  have hplus := hi.add tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero, add_zero] at hplus
  apply hplus.congr'
  filter_upwards [eventually_dim_pos] with q hq
  change (1 - binomialGap q (k q)/q)/2 + 1/q = _
  unfold binomialGap
  field_simp; ring

private theorem near_budgetTail {γ ε : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 4) :
    Tendsto (fun q => budgetTail q (k q) γ) atTop (𝓝 (Real.exp (ε/2)/2)) := by
  rw [← one_mul (Real.exp (ε/2))]
  apply budgetTail_limit hγ (hb.mono fun q b => (Real.sqrt_nonneg _).trans b.1)
    (scaledGap_threshold_ratio hγ (broad_of_near hb))
  have h := (scaledGap_near_threshold hγ hb).neg.div_const 2
  rw [neg_zero, zero_div] at h
  exact Real.tendsto_exp_nhds_zero_nhds_one.comp (h.congr fun q => by
    rw [neg_sub]; rfl)

private theorem far_budgetTail {γ ε : ℝ} (hγ : 1/2 < γ) {k : ℕ → ℕ}
    (hb : ∀ᶠ q : ℕ in atTop, thresholdRoot γ ε q + Real.sqrt q ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ thresholdRoot γ ε q + 10*Real.sqrt q) :
    Tendsto (fun q => budgetTail q (k q) γ) atTop (𝓝 0) := by
  have hlo := hb.mono fun q b => (le_add_of_nonneg_right (Real.sqrt_nonneg (q:ℝ))).trans b.1
  have h := budgetTail_limit (ε := ε) (b := 0) hγ
    (hlo.mono fun q b => (Real.sqrt_nonneg _).trans b)
    (scaledGap_threshold_ratio hγ (hb.mono fun q b => ⟨
      (le_add_of_nonneg_right (Real.sqrt_nonneg (q:ℝ))).trans b.1,b.2⟩))
  simp only [zero_mul, zero_div] at h
  apply h
  have hfar := (scaledGap_far_threshold hγ (hb.mono fun _ b => b.1)).const_mul_atTop
    (show (0:ℝ) < 1/2 by norm_num)
  exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp hfar).congr fun q => by
    dsimp [Function.comp_def, threshold]
    congr 1
    ring

private theorem normalized_reflected_budget {ternaryOnly : Bool} {q d k L : ℕ} {γ : ℝ} (hq : 0 < (q:ℝ))
    (hf : unrestrictedScheme ternaryOnly q d γ) (hr : d+2*k < q) (hL : L < k) :
    budgetTail q k γ * (((k:ℝ)+1)/q) +
      budgetTail q (k-1) γ * ((((k-1:ℕ):ℝ)+1)/q) -
      budgetTail q (k-L-1) γ * ((((k-L-1:ℕ):ℝ)+1)/q) ≤
      ((k:ℝ)+L+1)/q := by
  let factor : ℝ := (q:ℝ)^γ / ((q:ℝ)*(2:ℝ)^q)
  have e (j : ℕ) : budgetTail q j γ * (((j:ℝ)+1)/q) =
      weightedTail q j * factor := by
    dsimp [budgetTail, factor]
    field_simp
  rw [e, e, e, ← add_mul, ← sub_mul]
  have hf' : 0 ≤ factor := by dsimp [factor]; positivity
  have hb := mul_le_mul_of_nonneg_right (unrestricted_reflected_budget hf hr hL) hf'
  refine hb.trans_eq ?_
  push_cast
  unfold measurementBudget factor
  have hn := (Real.rpow_pos_of_pos hq γ).ne'
  field_simp [hn]

/-- The optimum's squared degree divided by dimension. -/
def asymmetricDegreeSquared (γ : ℝ) (q : ℕ) : ℝ :=
  (asymmetricDegree q γ : ℝ)^2/q

/-- The lower bound in (5), in its equivalent fixed-ε eventual form.
The measurements have no row-space invariance assumption. -/
theorem unrestricted_second_order_lower (ternaryOnly : Bool) {γ : ℝ} (hγ : 1/2 < γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, asymmetricLowerEndpoint γ q - ε ≤ (unrestrictedDegree ternaryOnly q γ : ℝ)^2/q := by
  let k := thresholdIndex γ ε
  let L := reflectLength
  let p := fun q : ℕ => k q-1
  let m := fun q : ℕ => k q-L q-1
  have data := cutoff_gap_data γ ε
  have hk := near_budgetTail (k := k) hγ (data.mono fun q h => h.1)
  have hp := near_budgetTail (k := p) hγ (data.mono fun q h => h.2.1)
  have hm := far_budgetTail (k := m) hγ (data.mono fun q h => h.2.2)
  have hkr := cutoff_index_ratio (k := k) (broad_of_near (data.mono fun q h => h.1))
  have hpr := cutoff_index_ratio (k := p) (broad_of_near (data.mono fun q h => h.2.1))
  have hmr := cutoff_index_ratio (k := m) (data.mono fun q h => ⟨
    (le_add_of_nonneg_right (Real.sqrt_nonneg (q:ℝ))).trans h.2.2.1, h.2.2.2⟩)
  have hL := hkr.add reflectLength_ratio
  rw [add_zero] at hL
  have total := (((hk.mul hkr).add (hp.mul hpr)).sub (hm.mul hmr)).sub hL
  have eq : (Real.exp (ε/2)/2*(1/2) + Real.exp (ε/2)/2*(1/2) - 0*(1/2) - 1/2) =
    (Real.exp (ε/2)-1)/2 := by ring
  rw [eq] at total
  have hpos : 0 < (Real.exp (ε/2)-1)/2 := by
    have he := Real.one_lt_exp_iff.mpr (show 0 < ε/2 by positivity)
    linarith
  filter_upwards [total.eventually (Ioi_mem_nhds hpos), cutoff_data γ ε,
    eventually_dim_pos] with q ht hc hq
  by_contra! bad
  have hdeg : (unrestrictedDegree ternaryOnly q γ : ℝ) ≤ thresholdRoot γ ε q := by
    unfold thresholdRoot
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    have he := (div_lt_iff₀ hq).mp bad
    have hn : 0 ≤ (q:ℝ)*threshold γ ε q := by
      change (unrestrictedDegree ternaryOnly q γ : ℝ)^2 < threshold γ ε q * q at he
      nlinarith [sq_nonneg (unrestrictedDegree ternaryOnly q γ : ℝ)]
    rw [Real.sq_sqrt hn]
    change (unrestrictedDegree ternaryOnly q γ : ℝ)^2 < threshold γ ε q * q at he
    linarith
  have hd : unrestrictedDegree ternaryOnly q γ ≤ ⌊thresholdRoot γ ε q⌋₊ := Nat.le_floor hdeg
  change ⌊thresholdRoot γ ε q⌋₊ + 2*k q < q ∧ L q < k q ∧ _ at hc
  have hr : unrestrictedDegree ternaryOnly q γ + 2*k q < q := by omega
  have hb := normalized_reflected_budget hq (unrestrictedDegree_feasible ternaryOnly q γ) hr hc.2.1
  change 0 < budgetTail q (k q) γ * (((k q:ℝ)+1)/q) +
    budgetTail q (p q) γ * (((p q:ℝ)+1)/q) -
    budgetTail q (m q) γ * (((m q:ℝ)+1)/q) -
    ((((k q:ℝ)+1)/q) + (L q:ℝ)/q) at ht
  have er : (((k q:ℝ)+1)/q) + (L q:ℝ)/q = ((k q:ℝ)+L q+1)/q := by
    rw [← add_div]
    congr 1
    ring
  rw [er] at ht
  exact (not_lt_of_ge hb) (sub_pos.mp ht)


/-- A vanishing error witnessing the lower inequality in (5). -/
theorem unrestricted_second_order_lower_error (ternaryOnly : Bool) {γ : ℝ} (hγ : 1/2 < γ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ q, asymmetricLowerEndpoint γ q + e q ≤ (unrestrictedDegree ternaryOnly q γ : ℝ)^2/q := by
  let e : ℕ → ℝ := fun q => min 0 ((unrestrictedDegree ternaryOnly q γ : ℝ)^2/q - asymmetricLowerEndpoint γ q)
  refine ⟨e, ?_, fun q => ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [unrestricted_second_order_lower ternaryOnly hγ (half_pos hε)] with q hq
    rw [Real.dist_eq, sub_zero, abs_lt]
    change -ε < min 0 _ ∧ min 0 _ < ε
    exact ⟨lt_min (by linarith) (by linarith), (min_le_left ..).trans_lt hε⟩
  · have h := min_le_right (0:ℝ) ((unrestrictedDegree ternaryOnly q γ : ℝ)^2/q - asymmetricLowerEndpoint γ q)
    change asymmetricLowerEndpoint γ q + min 0 _ ≤ _
    linarith

theorem unrestricted_sq_le_asymmetric (t : Bool) (q : ℕ) (γ : ℝ) :
    (unrestrictedDegree t q γ : ℝ)^2/q ≤ asymmetricDegreeSquared γ q := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (unrestrictedDegree_le_asymmetric t q γ)) 2

theorem asymmetric_second_order_lower {γ : ℝ} (hγ : 1/2 < γ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, asymmetricLowerEndpoint γ q - ε ≤ asymmetricDegreeSquared γ q :=
  (unrestricted_second_order_lower true hγ hε).mono fun q h => h.trans (unrestricted_sq_le_asymmetric true q γ)

theorem asymmetric_second_order_lower_error {γ : ℝ} (hγ : 1/2 < γ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ q, asymmetricLowerEndpoint γ q + e q ≤ asymmetricDegreeSquared γ q := by
  obtain ⟨e,he,h⟩ := unrestricted_second_order_lower_error true hγ
  exact ⟨e,he,fun q => (h q).trans (unrestricted_sq_le_asymmetric true q γ)⟩

end
end LocalReconstruction
