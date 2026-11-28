import V8NativeMessageN2PostBoundsScale
import P5MainBalanceM6SizeA
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000

/-! Uniform relative error of the original variable-marginal Xi bound:
sqrt(2 Q n)/(n/r) tends to zero on the actual printed MAIN schedule. -/
namespace V8NativeMessage.N2PostBounds
open Real Filter P5MainBalance P5MainBalance.M6
open scoped Topology

noncomputable section

def relativeError (n : ℕ) : ℝ :=
  (mainAlphabet n:ℝ)*sqrt (2*(mainNodes n:ℝ)*(n:ℝ))/(n:ℝ)

def errorCoeff : ℝ := sqrt 2*lambdaLogConstant

theorem relativeError_nonnegative (n : ℕ) : 0≤relativeError n := by
  unfold relativeError
  positivity

theorem nu_positive (n : ℕ) (hn : 2≤mainLambda n) :
    0 < mainNu n := by
  have hl : (2:ℝ)≤mainLambda n := by exact_mod_cast hn
  have hLog : 0 < log (mainLambda n:ℝ) := log_pos (one_lt_two.trans_le hl)
  have h := hLog.trans_le (log_le_mainNu n)
  exact_mod_cast h

theorem error_log_upper (n : ℕ) (hlog : 1≤log (n:ℝ))
    (hLam : 2≤mainLambda n) :
    relativeError n ≤ errorCoeff*(log (n:ℝ)/sqrt (n:ℝ)) := by
  let lam : ℝ := mainLambda n
  let r : ℝ := mainAlphabet n
  let Q : ℝ := mainNodes n
  let x : ℝ := n
  have hn : 0 < x := by
    have hn₀ : n≠0 := by rintro rfl; norm_num at hlog
    change 0 < (n:ℝ)
    exact_mod_cast Nat.pos_of_ne_zero hn₀
  have hr : r≤sqrt lam :=
    printed_alphabet_le_sqrt n (nu_positive n hLam)
  have hQ : Q≤lam := by
    change (mainNodes n:ℝ)≤(mainLambda n:ℝ)
    exact_mod_cast Nat.div_le_self (mainLambda n) (128*mainNu n)
  have hL0 : 0≤lam := by dsimp [lam]; positivity
  have hLamUpper : lam≤lambdaLogConstant*log x := lambda_le_literal_log n hlog
  have hRoot : sqrt (2*Q*x)≤sqrt 2*sqrt lam*sqrt x := by
    apply (sqrt_le_sqrt (show 2*Q*x≤2*lam*x by gcongr)).trans_eq
    rw [sqrt_mul (by positivity : 0≤2*lam),sqrt_mul (by norm_num : (0:ℝ)≤2)]
  have hProduct : r*sqrt (2*Q*x)≤sqrt 2*lam*sqrt x := by
    calc
      _ ≤ sqrt lam*(sqrt 2*sqrt lam*sqrt x) :=
        mul_le_mul hr hRoot (sqrt_nonneg _) (sqrt_nonneg _)
      _ = sqrt 2*(sqrt lam)^2*sqrt x := by ring
      _ = _ := by rw [sq_sqrt hL0]
  have hEq : sqrt x/x=1/sqrt x := by
    apply (div_eq_div_iff hn.ne' (sqrt_pos.2 hn).ne').2
    rw [←pow_two,sq_sqrt hn.le,one_mul]
  change r*sqrt (2*Q*x)/x≤errorCoeff*(log x/sqrt x)
  calc
    _ ≤ sqrt 2*lam*sqrt x/x := div_le_div_of_nonneg_right hProduct hn.le
    _ ≤ sqrt 2*(lambdaLogConstant*log x)*sqrt x/x := by gcongr
    _ = sqrt 2*(lambdaLogConstant*log x)*(sqrt x/x) := by ring
    _ = _ := by rw [hEq]; unfold errorCoeff; ring

theorem error_upper_tends_to_zero :
    Tendsto (fun n : ℕ=>errorCoeff*(log (n:ℝ)/sqrt (n:ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ=> log t / sqrt t) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : 0<(1/2:ℝ))).tendsto_div_nhds_zero
  have h' := h.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  simpa only [Function.comp_apply,mul_zero] using
    (tendsto_const_nhds (x:=errorCoeff) (f:=atTop)).mul h'

theorem relativeError_tends_to_zero :
    Tendsto relativeError atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun n=>ha.trans_le (relativeError_nonnegative n)
  · intro a ha
    have hLog := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually
      (eventually_ge_atTop (1:ℝ))
    filter_upwards [hLog,lambda_ge_along_sizes 2,
      error_upper_tends_to_zero.eventually (eventually_lt_nhds ha)] with n hn hLamLarge hsmall
    exact (error_log_upper n hn (by exact_mod_cast hLamLarge)).trans_lt hsmall

theorem exact_gap (N : ℕ) (hn : 0 < N) (hr : 0 < mainAlphabet (4*N)) :
    sqrt (2*(mainNodes (4*N):ℝ)*((4*N:ℕ):ℝ)) =
      relativeError (4*N)*wordMean N := by
  unfold relativeError wordMean
  have hn' : (0:ℝ)<((4*N:ℕ):ℝ) := by exact_mod_cast (show 0<4*N by omega)
  have hr' : (0:ℝ)<(mainAlphabet (4*N):ℝ) := by exact_mod_cast hr
  field_simp [hn'.ne',hr'.ne']

theorem published_gap_eventually_small (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,0 < mainAlphabet (4*N) ∧
      sqrt (2*(mainNodes (4*N):ℝ)*((4*N:ℕ):ℝ))≤ε*wordMean N := by
  have h := relativeError_tends_to_zero.eventually (eventually_le_nhds hε)
  filter_upwards [along_four_clones h,printed_mean_eventually,eventually_ge_atTop (1:ℕ)]
    with N he hr hN
  refine ⟨hr.1,?_⟩
  rw [exact_gap N (by omega) hr.1]
  exact mul_le_mul_of_nonneg_right he (by unfold wordMean; positivity)

#print axioms relativeError_nonnegative
#print axioms nu_positive
#print axioms error_log_upper
#print axioms error_upper_tends_to_zero
#print axioms relativeError_tends_to_zero
#print axioms exact_gap
#print axioms published_gap_eventually_small
end
end V8NativeMessage.N2PostBounds
