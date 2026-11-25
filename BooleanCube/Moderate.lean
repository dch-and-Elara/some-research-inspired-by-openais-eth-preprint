import BooleanCube.WeightedTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LocalReconstruction
open Filter Real
open scoped Topology
noncomputable section

def binomialGap (q k : ℕ) : ℝ := (q:ℝ)-2*k

def binomialMass (q k : ℕ) : ℝ := (q.choose k:ℝ)/(2:ℝ)^q

private theorem log_sq_div_nat : Tendsto (fun q : ℕ => (Real.log q)^2/(q:ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def,Real.rpow_one,Real.rpow_two] using h

theorem local_binomial_relative (k : ℕ → ℕ) (M : ℝ) (hM : 0 < M)
    (hw : ∀ᶠ q : ℕ in atTop, |(k q:ℝ)-q/2| ≤ M*Real.sqrt ((q:ℝ)*Real.log q)) :
    Tendsto (fun q : ℕ => binomialMass q (k q) * Real.sqrt (Real.pi*q/2) *
      Real.exp ((binomialGap q (k q))^2/(2*q))) atTop (𝓝 1) := by
  let err (q : ℕ) := Real.log (binomialMass q (k q)) -
    ((Real.log (2/Real.pi)-Real.log q)/2-2*((k q:ℝ)-q/2)^2/q)
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (g := fun q : ℕ => (3+4*M^2+48*M^4)*(Real.log q)^2/q)
      (Eventually.of_forall fun _ => abs_nonneg _)
    · filter_upwards [uniform_local_binomial M hM,hw] with q h w using h (k q) w
    · simpa only [mul_zero,mul_div_assoc] using log_sq_div_nat.const_mul (3+4*M^2+48*M^4)
  have ex := Real.continuous_exp.continuousAt.tendsto.comp herr
  rw [Real.exp_zero] at ex
  apply ex.congr'
  filter_upwards [hw,eventually_ge_atTop 1, (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (gt_mem_nhds (show 0 < 1/(4*M^2) by positivity))] with q w hq small
  have hq' : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have hL : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  change Real.log q/(q:ℝ) < 1/(4*M^2) at small
  have s := (div_lt_div_iff₀ hq' (show 0<4*M^2 by positivity)).mp small
  have b := sq_le_sq.mpr (show |(k q:ℝ)-q/2| ≤ |M*Real.sqrt ((q:ℝ)*Real.log q)| by
    rwa [abs_of_nonneg (mul_nonneg hM.le (Real.sqrt_nonneg _))])
  rw [mul_pow,Real.sq_sqrt (mul_nonneg hq'.le hL)] at b
  have hle : k q ≤ q := by
    by_contra! no
    have hb : (q:ℝ) < k q := by exact_mod_cast no
    nlinarith [mul_lt_mul_of_pos_left s hq',mul_pos (sub_pos.mpr hb) (show 0<(k q:ℝ) by linarith)]
  have hm : 0 < binomialMass q (k q) := div_pos (by exact_mod_cast Nat.choose_pos hle) (by positivity)
  have hj : (Real.log (2/Real.pi)-Real.log q)/2 = -Real.log (Real.sqrt (Real.pi*q/2)) := by
    rw [Real.log_sqrt (by positivity),Real.log_div (mul_pos Real.pi_pos hq').ne' (by norm_num),
      Real.log_mul Real.pi_pos.ne' hq'.ne',Real.log_div (by norm_num) Real.pi_pos.ne']
    ring
  have hg : 2*((k q:ℝ)-q/2)^2/q = (binomialGap q (k q))^2/(2*q) := by
    unfold binomialGap; field_simp; ring
  change Real.exp (err q) = _
  dsimp only [err]
  rw [hj,hg,show ∀ a b c : ℝ, a - (-b-c) = a+b+c by intros; ring,
    Real.exp_add,Real.exp_add,Real.exp_log hm,Real.exp_log (by positivity)]

private theorem nat_log_top : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem moderate_scales (k : ℕ → ℕ) (m M : ℝ) (hm : 0 < m) (_hM : 0 < M)
    (hw : ∀ᶠ q : ℕ in atTop, m*Real.sqrt ((q:ℝ)*Real.log q) ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ M*Real.sqrt ((q:ℝ)*Real.log q)) :
    Tendsto (fun q : ℕ => binomialGap q (k q)/q) atTop (𝓝 0) ∧
    Tendsto (fun q : ℕ => (q:ℝ)/(binomialGap q (k q))^2) atTop (𝓝 0) ∧
    Tendsto (fun q : ℕ => binomialGap q (k q)) atTop atTop := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hg : ∀ᶠ q : ℕ in atTop, 0 < binomialGap q (k q) := by
    filter_upwards [hw,nat_log_top.eventually_gt_atTop 0,eventually_ge_atTop 1] with q w l hq
    have qp : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
    exact lt_of_lt_of_le (mul_pos hm (Real.sqrt_pos.mpr (mul_pos qp l))) w.1
  refine ⟨?_,?_,?_⟩
  · apply squeeze_zero' (g := fun q : ℕ => M*Real.sqrt (Real.log q/q))
      (hg.mono fun q h => div_nonneg h.le (Nat.cast_nonneg _))
    · filter_upwards [hw,eventually_ge_atTop 1] with q w hq
      have qp : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
      have e : Real.sqrt ((q:ℝ)*Real.log q) = (q:ℝ)*Real.sqrt (Real.log q/q) := by
        calc
          _ = Real.sqrt ((q:ℝ)^2*(Real.log q/q)) := by congr 1; field_simp
          _ = _ := by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq qp.le]
      rw [e] at w
      exact (div_le_iff₀ qp).mpr (by nlinarith [w.2])
    · simpa using ((Real.continuous_sqrt.tendsto 0).comp hlim).const_mul M
  · apply squeeze_zero' (g := fun q : ℕ => 1/(m^2*Real.log q))
      (Eventually.of_forall fun q => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    · filter_upwards [hw,nat_log_top.eventually_gt_atTop 0,eventually_ge_atTop 1] with q w l hq
      have qp : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
      have z := mul_self_le_mul_self (mul_nonneg hm.le (Real.sqrt_nonneg _)) w.1
      have e := Real.sq_sqrt (mul_nonneg qp.le l.le)
      have gp : 0 < binomialGap q (k q) := (mul_pos hm (Real.sqrt_pos.mpr (mul_pos qp l))).trans_le w.1
      apply (div_le_div_iff₀ (sq_pos_of_pos gp) (mul_pos (sq_pos_of_pos hm) l)).mpr
      nlinarith only [z,congrArg (fun x => m^2*x) e]
    · simpa only [zero_mul,one_div,mul_inv_rev,Function.comp_def] using
        ((tendsto_inv_atTop_zero.comp nat_log_top).mul_const (m^2)⁻¹)
  · have hprod := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_atTop₀ nat_log_top
    exact tendsto_atTop_mono' atTop (hw.mono fun _ h => h.1)
      ((Real.tendsto_sqrt_atTop.comp hprod).const_mul_atTop hm)

/-- Equation (21) as convergence of the quotient to one, for arbitrary integer k(q)
in any fixed two-sided moderate-deviation window. -/
theorem weighted_binomial_asymptotic (k : ℕ → ℕ) (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hw : ∀ᶠ q : ℕ in atTop, m*Real.sqrt ((q:ℝ)*Real.log q) ≤ binomialGap q (k q) ∧
      binomialGap q (k q) ≤ M*Real.sqrt ((q:ℝ)*Real.log q)) :
    Tendsto (fun q : ℕ =>
      weightedTail q (k q) / (((k q:ℝ)+1)*(2:ℝ)^q) *
        (Real.sqrt (2*Real.pi*q) * ((binomialGap q (k q))^2/q) *
          Real.exp ((binomialGap q (k q))^2/(2*q)))) atTop (𝓝 1) := by
  let g := fun q => binomialGap q (k q)
  let A := fun q : ℕ => (q:ℝ)-k q+1
  let u := fun q => (g q+1)^2*weightedTail q (k q)/((A q)^2*q.choose (k q))
  obtain ⟨hrel,hscale,hgrow⟩ := moderate_scales k m M hm hM hw
  have hq : ∀ᶠ q : ℕ in atTop, 0 < (q:ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hk : Tendsto (fun q : ℕ => (k q:ℝ)/q) atTop (𝓝 (1/2:ℝ)) := by
    have e := (tendsto_const_nhds (x := (1:ℝ))).sub hrel
    apply (show Tendsto (fun q : ℕ => (1-g q/q)/2) atTop (𝓝 (1/2:ℝ)) by
      simpa only [sub_zero] using e.div_const 2).congr'
    filter_upwards [hq] with q h
    dsimp [g,binomialGap]; field_simp; ring
  have hA : Tendsto (fun q : ℕ => A q/q) atTop (𝓝 (1/2:ℝ)) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ))).sub hk).add tendsto_one_div_atTop_nhds_zero_nat
    apply (show Tendsto (fun q : ℕ => 1-(k q:ℝ)/q+1/q) atTop (𝓝 (1/2:ℝ)) by convert h using 1; norm_num).congr'
    filter_upwards [hq] with q h
    dsimp [A]; field_simp
  have hplus : Tendsto (fun q : ℕ => (g q+1)/g q) atTop (𝓝 1) := by
    have h := (tendsto_inv_atTop_zero.comp hgrow).const_add 1
    apply (show Tendsto (fun q => 1+(g q)⁻¹) atTop (𝓝 1) by simpa using h).congr'
    filter_upwards [hgrow.eventually_gt_atTop 0] with q h
    have : g q ≠ 0 := h.ne'
    field_simp
  have hsmall : Tendsto (fun q : ℕ => 6*A q/(g q+1)^2) atTop (𝓝 0) := by
    have h := ((hA.mul hscale).div (hplus.pow 2) (by norm_num)).const_mul 6
    apply (show Tendsto (fun q : ℕ => 6*((A q/q * ((q:ℝ)/(g q)^2))/(((g q+1)/g q)^2)))
        atTop (𝓝 0) by simpa only [mul_zero,zero_div] using h).congr'
    filter_upwards [hq,hgrow.eventually_gt_atTop 0] with q qp gp
    have gn : g q ≠ 0 := gp.ne'
    have gn' : g q+1 ≠ 0 := by change 0 < g q at gp; positivity
    field_simp
  have hu : Tendsto u atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).div (hsmall.const_add 1) (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := u)
      (show Tendsto (fun q => 1/(1+6*A q/(g q+1)^2)) atTop (𝓝 1) by
        change Tendsto ((fun _ : ℕ => (1:ℝ)) / (fun q => 1+6*A q/(g q+1)^2)) atTop _
        convert h using 1; norm_num)
      (tendsto_const_nhds (x := (1:ℝ)))
    all_goals
      filter_upwards [hgrow.eventually_gt_atTop 0] with q hg
      change 0 < (q:ℝ)-2*(k q:ℝ) at hg
      have he : 2*k q ≤ q := by exact_mod_cast (show 2*(k q:ℝ) ≤ q by linarith)
      have ce : 0 < (q.choose (k q):ℝ) := by exact_mod_cast Nat.choose_pos (show k q ≤ q by omega)
      have ap : 0 < A q := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) (k q)]
      have gp : 0 < g q+1 := by dsimp [g,binomialGap]; linarith
      have b := weighted_tail_sandwich he
      change (g q+1)^2*weightedTail q (k q) ≤ (A q)^2*q.choose (k q) ∧
        (A q)^2*q.choose (k q) ≤ ((g q+1)^2+6*A q)*weightedTail q (k q) at b
      dsimp only [u]
    · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      field_simp
      simpa only [mul_comm (weightedTail q (k q)), mul_comm (A q) 6] using b.2
    · exact (div_le_one (mul_pos (sq_pos_of_pos ap) ce)).mpr b.1
  have hk1 := hk.add tendsto_one_div_atTop_nhds_zero_nat
  have hk' : Tendsto (fun q : ℕ => ((k q:ℝ)+1)/q) atTop (𝓝 (1/2:ℝ)) := by
    simpa only [add_div,add_zero] using hk1
  have loc := local_binomial_relative k M hM (by
    filter_upwards [hw] with q w
    rw [abs_le]
    have h := mul_nonneg hm.le (Real.sqrt_nonneg ((q:ℝ)*Real.log q))
    have g0 := h.trans w.1
    unfold binomialGap at g0 w
    constructor <;> linarith [w.2,mul_nonneg hM.le (Real.sqrt_nonneg ((q:ℝ)*Real.log q))])
  have total := (((((hu.mul (hA.pow 2)).div (hplus.pow 2) (by norm_num)).div hk' (by norm_num)).mul loc).const_mul 2)
  have limit : (2:ℝ)*(1*(1/2)^2/1^2/(1/2)*1) = 1 := by norm_num
  rw [limit] at total
  apply total.congr'
  filter_upwards [hq,hgrow.eventually_gt_atTop 0] with q qp gp
  change 0 < (q:ℝ)-2*(k q:ℝ) at gp
  have gn : g q ≠ 0 := ne_of_gt gp
  have gn' : g q+1 ≠ 0 := by dsimp [g,binomialGap]; linarith
  have an : A q ≠ 0 := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) (k q)]
  have ce : (q.choose (k q):ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show k q ≤ q by exact_mod_cast (show (k q:ℝ) ≤ q by
      linarith [Nat.cast_nonneg (α := ℝ) (k q)]))).ne'
  have root : Real.sqrt (2*Real.pi*q) = 2*Real.sqrt (Real.pi*q/2) := by
    rw [show 2*Real.pi*q=4*(Real.pi*q/2) by ring,Real.sqrt_mul (by norm_num)]; norm_num
  simp only [Pi.div_apply,u,binomialMass,root]
  change 2*(((g q+1)^2*weightedTail q (k q)/((A q)^2*q.choose (k q))*(A q/q)^2/((g q+1)/g q)^2/
    (((k q:ℝ)+1)/q))*(q.choose (k q)/(2:ℝ)^q*Real.sqrt (Real.pi*q/2)*Real.exp ((g q)^2/(2*q)))) = _
  field_simp; ring

end
end LocalReconstruction
