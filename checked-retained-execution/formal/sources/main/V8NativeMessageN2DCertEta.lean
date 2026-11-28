import V8NativeMessageN2DCertScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 19000000

/-! Original v8 line 2237 for the actual printed quantities, with an
explicit constant and no asymptotic assumption about the cutoff. -/
namespace V8NativeMessage.N2DCert
open Real Filter Paper5.HybridClosure.Printed J1PPrinted J9PrintedSchedule
open scoped Topology

noncomputable section

def etaCoeff : ℝ := 2*(2/log 2)^(1/4:ℝ)

theorem etaCoeff_pos : 0 < etaCoeff := by
  unfold etaCoeff
  have h := log_pos (by norm_num : (1:ℝ)<2)
  positivity

theorem eta_printed_rate (s : ℕ) (hs : 2≤s) :
    eta s≤etaCoeff*(s:ℝ)^(-49/1000:ℝ)*(log (s:ℝ))^(1/4:ℝ) := by
  let x : ℝ := s
  let lam : ℝ := Nat.clog 2 s
  let Δ : ℝ := sourceDelta s
  let H : ℝ := nativeH s
  have hx : 0 < x := by
    change (0:ℝ)<s
    exact_mod_cast (show 0<s by omega)
  have hH : 0 < H := by
    change (0:ℝ)<nativeH s
    exact_mod_cast (threshold_real_cover s hs).1
  have hlog : 0 < log x := log_pos (by
    change (1:ℝ)<s
    exact_mod_cast (show 1<s by omega))
  have hLam0 : 0≤lam := by unfold lam; positivity
  have hΔ := delta_double_upper s (by omega)
  have hInv := threshold_inverse_upper s hs
  have he : 2*Δ/H≤4*x^(-1/10:ℝ)*sqrt lam := by
    calc
      _ ≤ 4*x^(9/10:ℝ)/H :=
        div_le_div_of_nonneg_right (by
          change 2*(sourceDelta s:ℝ)≤4*(s:ℝ)^(9/10:ℝ)
          linarith only [hΔ]) hH.le
      _ = (4*x^(9/10:ℝ))*(1/H) := by ring
      _ ≤ (4*x^(9/10:ℝ))*(sqrt lam/x) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = 4*(x^(9/10:ℝ)/x)*sqrt lam := by ring
      _ = _ := by rw [←rpow_sub_one hx.ne']; norm_num
  have hxpow : sqrt (x^(-1/10:ℝ))=x^(-1/20:ℝ) := by
    rw [sqrt_eq_rpow,←rpow_mul hx.le]
    norm_num
  have hlamPow : sqrt (sqrt lam)=lam^(1/4:ℝ) := by
    rw [sqrt_eq_rpow (sqrt lam),sqrt_eq_rpow lam,←rpow_mul hLam0]
    norm_num
  have hSqrt : sqrt (2*Δ/H)≤2*x^(-1/20:ℝ)*lam^(1/4:ℝ) := by
    apply (sqrt_le_sqrt he).trans_eq
    rw [sqrt_mul (by positivity : 0≤4*x^(-1/10:ℝ)),
      sqrt_mul (by norm_num : (0:ℝ)≤4),hxpow,hlamPow]
    norm_num
  have hBasic : eta s≤2*x^(-49/1000:ℝ)*lam^(1/4:ℝ) := by
    change x^(1/1000:ℝ)*sqrt (2*Δ/H)≤_
    calc
      _ ≤ x^(1/1000:ℝ)*(2*x^(-1/20:ℝ)*lam^(1/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hSqrt (by positivity)
      _ = 2*(x^(1/1000:ℝ)*x^(-1/20:ℝ))*lam^(1/4:ℝ) := by ring
      _ = _ := by rw [←rpow_add hx]; norm_num
  have hC : 0 < (2:ℝ)/log 2 := div_pos (by norm_num) (log_pos (by norm_num))
  have hL : lam≤(2/log 2)*log x := by
    simpa [lam,x] using clog_real_log_bound s s 1 hs (by omega) (by simp)
  have hL' := rpow_le_rpow hLam0 hL (by norm_num : 0≤(1/4:ℝ))
  rw [mul_rpow hC.le hlog.le] at hL'
  calc
    _ ≤ 2*x^(-49/1000:ℝ)*lam^(1/4:ℝ) := hBasic
    _ ≤ 2*x^(-49/1000:ℝ)*((2/log 2)^(1/4:ℝ)*(log x)^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_left hL' (by positivity)
    _ = _ := by unfold etaCoeff; dsimp [x]; ring

theorem eta_printed_tends_to_zero : Tendsto eta atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ=>(log x)^(1/4:ℝ)/x^(49/1000:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (1/4) (by norm_num : 0<(49/1000:ℝ))).tendsto_div_nhds_zero
  have hC : Tendsto (fun s : ℕ=>etaCoeff*((log (s:ℝ))^(1/4:ℝ)/(s:ℝ)^(49/1000:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      (h.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul etaCoeff
  have h' : Tendsto (fun s : ℕ=>etaCoeff*(s:ℝ)^(-49/1000:ℝ)*(log (s:ℝ))^(1/4:ℝ)) atTop (𝓝 0) := by
    apply hC.congr'
    refine Eventually.of_forall fun s=>?_
    change etaCoeff*((log (s:ℝ))^(1/4:ℝ)/(s:ℝ)^(49/1000:ℝ)) =
      etaCoeff*(s:ℝ)^(-49/1000:ℝ)*(log (s:ℝ))^(1/4:ℝ)
    rw [show (-49/1000:ℝ)=-(49/1000:ℝ) by ring,
      rpow_neg (show (0:ℝ)≤(s:ℝ) by positivity) (49/1000:ℝ),div_eq_mul_inv]
    ring
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun s=>ha.trans_le (eta_nonnegative s)
  · intro a ha
    filter_upwards [eventually_ge_atTop (2:ℕ),h'.eventually (eventually_lt_nhds ha)] with s hs hsmall
    exact (eta_printed_rate s hs).trans_lt hsmall

#print axioms etaCoeff_pos
#print axioms eta_printed_rate
#print axioms eta_printed_tends_to_zero
end
end V8NativeMessage.N2DCert
