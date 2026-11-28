import V8NativeMessageN5AsymptoticTransfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4700000

/-! The exact two eventual inequalities in v8 N5, quantitative in
the fixed expansion and any fixed polynomial delivery width. -/
namespace V8NativeMessage.N5
open scoped BigOperators Topology
open Filter Paper5.HybridClosure Paper5.HybridClosure.Printed
noncomputable section

def oneScale (N : ℕ) : ℝ :=
  (N:ℝ)*(Real.log (Real.log (N:ℝ)))^2/Real.sqrt (Real.log (N:ℝ))

def menuScale (N : ℕ) : ℝ :=
  (N:ℝ)*(Real.log (Real.log (N:ℝ)))^2/Real.log (N:ℝ)

def oneCoefficient (γ : ℝ) : ℝ := γ/68/(4*Real.sqrt printedLogConst)

def menuCoefficient (γ : ℚ) : ℝ := menuSlope γ/(4*Real.sqrt printedLogConst)

theorem one_coefficient_positive (γ : ℝ) (hγ : 0<γ) :
    0<oneCoefficient γ := by
  have hC := printed_log_const_pos
  unfold oneCoefficient
  positivity

theorem menu_coefficient_positive (γ : ℚ) (hγ : 0<γ) :
    0<menuCoefficient γ := by
  have hC := printed_log_const_pos
  have hc := menu_slope_positive γ hγ
  unfold menuCoefficient
  positivity

theorem original_single_scale_eventually (γ : ℝ) (hγ : 0<γ) (coeff e : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ width T : ℕ,
      0<width → width≤coeff*(N+1)^e →
      (γ*(N:ℝ)/68-Real.logb 2 ((12*N+1:ℕ):ℝ))/(mainR N+1)-
        Real.logb 2 width≤Real.logb 2 T →
      oneCoefficient γ*oneScale N≤Real.logb 2 T := by
  let c : ℝ := γ/68
  have hc : 0<c := by dsimp [c]; positivity
  let E : ℕ := e+1
  have small := eventual_square_lambda_small (4*((E:ℝ)+1)) c (by positivity) hc
  filter_upwards [eventual_printed_MAIN_N5,small,eventually_ge_atTop coeff] with N hN hsmall hcoeff
  intro width T hw hwpoly hwork
  have hN₁ : 1≤N := by omega
  have hS : 1≤Real.sqrt (mainLambda N:ℝ) := by
    rw [←Real.sqrt_one]
    exact Real.sqrt_le_sqrt (hN.2.1.trans (printed_lambda_lower N hN₁))
  have hLarge : c*(N:ℝ)/Real.sqrt (mainLambda N:ℝ)≤γ*(N:ℝ)/68 := by
    rw [show γ*(N:ℝ)/68=c*(N:ℝ) by unfold c; ring]
    apply (div_le_iff₀ (zero_lt_one.trans_le hS)).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ)≤c*N)
  have hMain := printed_asymptotic_scale N E width T c (γ*(N:ℝ)/68) hc hN₁ hN.2.1
    hN.2.2 hw (polynomial_coefficient_absorb N e coeff width (by omega) hwpoly) hsmall hLarge hwork
  calc
    _ = (γ*(N:ℝ)/68)*(Real.log (Real.log (N:ℝ)))^2/
        (4*Real.sqrt printedLogConst*Real.sqrt (Real.log (N:ℝ))) := by
      unfold oneCoefficient oneScale
      ring
    _ ≤ _ := hMain

theorem original_menu_scale_eventually (γ : ℚ) (hγ : 0<γ) (coeff e : ℕ) :
    ∀ᶠ N : ℕ in atTop, 0<dU N ∧
      31104*(dU N:ℚ)^2<(matchingCoeff γ)^2*(N:ℚ) ∧
      ∀ width T : ℕ, 0<width → width≤coeff*(N+1)^e →
      ((routeDepth γ N (dU N):ℝ)-Real.logb 2 ((12*N+1:ℕ):ℝ))/(mainR N+1)-
        Real.logb 2 width≤Real.logb 2 T →
      menuCoefficient γ*menuScale N≤Real.logb 2 T := by
  let c := menuSlope γ
  have hc : 0<c := menu_slope_positive γ hγ
  let E : ℕ := e+1
  have small := eventual_square_lambda_small (4*((E:ℝ)+1)) c (by positivity) hc
  filter_upwards [eventual_printed_MAIN_N5, eventual_actual_menu γ hγ,small,
    eventually_ge_atTop coeff] with N hN hMenu hsmall hcoeff
  refine ⟨hMenu.1,hMenu.2.1,?_⟩
  intro width T hw hwpoly hwork
  have hN₁ : 1≤N := by omega
  let a : ℝ := routeDepth γ N (dU N)
  have hS : 0<Real.sqrt (Real.log (N:ℝ)) :=
    Real.sqrt_pos_of_pos (zero_lt_one.trans_le hN.2.1)
  have hLarge : c*(N:ℝ)/Real.sqrt (mainLambda N:ℝ)≤a := by
    have h := div_le_div_of_nonneg_left (by positivity : (0:ℝ)≤c*(N:ℝ)) hS
      (Real.sqrt_le_sqrt (printed_lambda_lower N hN₁))
    exact h.trans (by rw [mul_div_assoc]; exact hMenu.2.2)
  have hMain := printed_asymptotic_scale N E width T c a hc hN₁ hN.2.1
    hN.2.2 hw (polynomial_coefficient_absorb N e coeff width (by omega) hwpoly) hsmall hLarge hwork
  let l := Real.log (N:ℝ)
  let b := Real.log l
  let s := Real.sqrt l
  let q := Real.sqrt printedLogConst
  have hs2 : s^2=l := Real.sq_sqrt (zero_le_one.trans hN.2.1)
  have hq : 0<q := Real.sqrt_pos_of_pos printed_log_const_pos
  have hs : 0<s := hS
  calc
    _ = (c*((N:ℝ)/s))*b^2/(4*q*s) := by
      change (c/(4*q))*((N:ℝ)*b^2/l)=_ 
      rw [←hs2]
      field_simp
    _ ≤ a*b^2/(4*q*s) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMenu.2.2 (sq_nonneg b)) (by positivity)
    _ ≤ _ := hMain

#print axioms one_coefficient_positive
#print axioms menu_coefficient_positive
#print axioms original_single_scale_eventually
#print axioms original_menu_scale_eventually
end
end V8NativeMessage.N5