import V8NativeMessageN5Printed
import P5HybridClosurePrintedGrowth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! Numerical asymptotics at the actual printed v8 N5 root sizes.
This file does not assert that any algorithm follows a charged trace. -/
namespace V8NativeMessage.N5
open scoped BigOperators Topology
open Filter Paper5.HybridClosure Paper5.HybridClosure.Printed
noncomputable section

theorem log_le_log_two (x : ℝ) (hx : 1≤x) : Real.log x≤Real.logb 2 x := by
  have h2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have h₂ : Real.log (2:ℝ)≤1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  unfold Real.logb
  exact (le_div_iff₀ h2).2 (by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left h₂ (Real.log_nonneg hx))

theorem printed_lambda_upper (N : ℕ) (hN : 2≤N) :
    (mainLambda N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
  have hN' : 4*N≤N^3 := by
    calc
      _ ≤ N^2*N := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
      _ = _ := (pow_succ _ _).symm
  have h := clog_real_log_bound N (4*N) 3 hN (by omega) hN'
  change (mainLambda N:ℝ)≤_ at h
  refine h.trans ?_
  have h2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hN₁ : (1:ℝ)≤N := by exact_mod_cast (by omega : 1≤N)
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num :
    (((3+1:ℕ):ℝ))≤6) h2) (Real.log_nonneg hN₁)

theorem printed_lambda_lower (N : ℕ) (hN : 1≤N) :
    Real.log (N:ℝ)≤mainLambda N := by
  have hN₁ : (1:ℝ)≤N := by exact_mod_cast hN
  have hx : (N:ℝ)≤((4*N:ℕ):ℝ) := by exact_mod_cast (by omega : N≤4*N)
  have h := Real.logb_le_logb_of_le (b:=2) (by norm_num) (zero_lt_one.trans_le hN₁) hx
  rw [main_lambda_literal]
  exact (log_le_log_two _ hN₁).trans (h.trans (Nat.le_ceil _))

theorem printed_nu_lower (N : ℕ) (hN : 1≤N) (hL : 1≤Real.log (N:ℝ)) :
    Real.log (Real.log (N:ℝ))≤mainNu N := by
  have h := Real.logb_le_logb_of_le (b:=2) (by norm_num)
    (zero_lt_one.trans_le hL) (printed_lambda_lower N hN)
  rw [main_nu_literal]
  exact (log_le_log_two _ hL).trans (h.trans (Nat.le_ceil _))

theorem printed_nu_pos (N : ℕ) (hr : 1≤mainR N) : 0<mainNu N := by
  by_contra! h
  have hz : mainNu N=0 := by omega
  unfold mainR at hr
  rw [hz,zero_pow (by decide : (2:ℕ)≠0),Nat.div_zero] at hr
  omega

theorem printed_output_log_ceilings (N : ℕ) (hN : 1≤N) :
    Real.logb 2 ((12*N+1:ℕ):ℝ)≤2*(mainLambda N:ℝ) ∧
      Real.logb 2 ((N+1:ℕ):ℝ)≤mainLambda N := by
  have hN₁ : (1:ℝ)≤N := by exact_mod_cast hN
  have hCeil : Real.logb 2 ((4*N:ℕ):ℝ)≤mainLambda N := by
    rw [main_lambda_literal]
    exact Nat.le_ceil _
  have h1 : ((12*N+1:ℕ):ℝ)≤(((4*N:ℕ):ℝ))^2 := by
    push_cast
    have h := mul_nonneg (by positivity : (0:ℝ)≤N) (sub_nonneg.mpr hN₁)
    nlinarith only [h,hN₁]
  have h2 : ((N+1:ℕ):ℝ)≤((4*N:ℕ):ℝ) := by exact_mod_cast (by omega : N+1≤4*N)
  constructor
  · have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) (by positivity) h1
    rw [Real.logb_pow] at hlog
    exact hlog.trans (mul_le_mul_of_nonneg_left hCeil (by norm_num))
  · exact (Real.logb_le_logb_of_le (b:=2) (by norm_num) (by positivity) h2).trans hCeil

theorem eventual_printed_MAIN_N5 :
    ∀ᶠ N : ℕ in atTop, 2≤N ∧ 1≤Real.log (N:ℝ) ∧ 1≤mainR N := by
  have hLog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),
    hLog.eventually (eventually_ge_atTop (1:ℝ)),main_printed_eventual] with N hN hL hr
  exact ⟨hN,hL,by have h := hr.1; omega⟩

theorem eventual_square_lambda_small (D c : ℝ) (hD : 0≤D) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, D*(mainLambda N:ℝ)^2≤c*(N:ℝ) := by
  have ht : Tendsto (fun x : ℝ=>Real.log x^2/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have htNat := ht.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  let C := printedLogConst
  have hC : 0<C := printed_log_const_pos
  have hcoef : Tendsto (fun N : ℕ=>D*C^2*(Real.log (N:ℝ)^2/(N:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using htNat.const_mul (D*C^2)
  filter_upwards [hcoef.eventually (Iio_mem_nhds hc),eventual_printed_MAIN_N5] with N hS hN
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hupper := printed_lambda_upper N hN.1
  have hs : D*C^2*Real.log (N:ℝ)^2<c*(N:ℝ) := by
    change D*C^2*(Real.log (N:ℝ)^2/(N:ℝ))<c at hS
    rw [←mul_div_assoc] at hS
    exact (div_lt_iff₀ hNp).1 hS
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤mainLambda N) hupper 2
  calc
    _ ≤ D*(C*Real.log (N:ℝ))^2 := mul_le_mul_of_nonneg_left hp hD
    _ = D*C^2*Real.log (N:ℝ)^2 := by ring
    _ ≤ _ := hs.le

noncomputable def menuSlope (γ : ℚ) : ℝ :=
  (matchingCoeff γ:ℝ)/(4*Real.sqrt printedLogConst)

theorem menu_slope_positive (γ : ℚ) (hγ : 0<γ) : 0<menuSlope γ := by
  unfold menuSlope
  have hc : (0:ℝ)<(matchingCoeff γ:ℚ) := by exact_mod_cast matchingCoeff_pos γ hγ
  have hC := printed_log_const_pos
  positivity

theorem eventual_actual_menu (γ : ℚ) (hγ : 0<γ) :
    ∀ᶠ N : ℕ in atTop,
      0<dU N ∧ 31104*(dU N:ℚ)^2<(matchingCoeff γ)^2*(N:ℚ) ∧
      menuSlope γ*((N:ℝ)/Real.sqrt (Real.log (N:ℝ)))≤routeDepth γ N (dU N) := by
  have hU : ∀ᶠ N : ℕ in atTop, 0<dU N ∧
      (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
    filter_upwards [d_printed_eventual,eventually_ge_atTop (2:ℕ)] with N hu hN
    exact ⟨hu.2.1,(printed_logarithmic_widths N hN).2⟩
  have hlog : ∀ᶠ N : ℕ in atTop,
      (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) ∧
      (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) :=
    hU.mono (fun _ h => ⟨h.2,h.2⟩)
  have hcoef : (0:ℝ)<(matchingCoeff γ:ℚ) := by exact_mod_cast matchingCoeff_pos γ hγ
  have hb := log_scale_gives_eventual_union dU dU printedLogConst
    (matchingCoeff γ:ℝ) hcoef hlog
  have hdepth := log_schedules_bigOmega_depth dU dU γ hγ printedLogConst
    printed_log_const_pos (hU.mono (fun _ h => ⟨h.1,h.1,h.2,h.2⟩))
  filter_upwards [hU,hb,hdepth] with N hu hb hd
  refine ⟨hu.1,?_,?_⟩
  · have hf : 31104*(dU N:ℝ)^2<(matchingCoeff γ:ℝ)^2*(N:ℝ) := by
      nlinarith only [hb,sq_nonneg (dU N:ℝ)]
    exact_mod_cast hf
  · simpa only [menuSlope,min_self] using hd

#print axioms printed_lambda_upper
#print axioms printed_lambda_lower
#print axioms printed_nu_lower
#print axioms printed_output_log_ceilings
#print axioms eventual_printed_MAIN_N5
#print axioms eventual_square_lambda_small
#print axioms eventual_actual_menu
end
end V8NativeMessage.N5