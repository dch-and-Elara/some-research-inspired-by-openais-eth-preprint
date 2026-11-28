import P5MainBalanceNodeGrowth
import P5MainBalanceExponentRoom

/-! Polynomially many source coefficient addresses and polynomial
register overhead are negligible on the true printed N/sqrt Q scale. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Filter Real P5MainIterator

set_option maxHeartbeats 8000000 in
theorem printed_polynomial_overhead_small (a p : ℕ) (ha : 0<a)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ N, n≤a*N → 0<mainNodes n →
      (n:ℝ)^p < exp (ε*(N:ℝ)/sqrt (mainNodes n:ℝ)) := by
  let K := logEightBound+1
  have hK1 : 1≤K := by
    have hlog2 : 0<log 2 := log_pos (by norm_num)
    dsimp [K,logEightBound]
    linarith only [(show 0≤8/log 2 by positivity)]
  let A := (8*(p:ℝ)*K*(a:ℝ))/ε+2
  have ha' : 0<(a:ℝ) := by exact_mod_cast ha
  have hK0 : 0<K := by linarith only [hK1]
  have hA2 : 2≤A := by
    dsimp [A]
    linarith only [(show 0≤8*(p:ℝ)*K*(a:ℝ)/ε by positivity)]
  have hA1 : 1≤A := by linarith only [hA2]
  have hEvent := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (A^8))
  filter_upwards [hEvent] with n hn
  intro N hN hQ
  let z := eighth (n:ℝ)
  have hzA : A≤z := by
    rw [←eighth_pow_inverse A (by linarith only [hA1])]
    exact eighth_mono hn
  have hz1 : 1≤z := hA1.trans hzA
  have hz : 0<z := by linarith only [hz1]
  have hn1 : 1≤(n:ℝ) := (one_le_pow₀ hA1).trans hn
  have hn' : 0<(n:ℝ) := by linarith only [hn1]
  have hQ' : 0<(mainNodes n:ℝ) := by exact_mod_cast hQ
  have hN' : (n:ℝ)≤(a:ℝ)*(N:ℝ) := by exact_mod_cast hN
  have hq0 : (mainNodes n:ℝ)≤(mainLambda n:ℝ) := by exact_mod_cast Nat.div_le_self (mainLambda n) (128*mainNu n)
  have hq1 := hq0.trans (ceil_logTwo_le (n:ℝ) hn1)
  have hq2 : (mainNodes n:ℝ)≤(K*z)^2 := by
    have hK : logEightBound≤K := by dsimp [K]; linarith
    have hzK : 1≤K*z := by
      calc
        _ ≤ K := hK1
        _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 hK0.le
    apply hq1.trans
    exact (mul_le_mul_of_nonneg_right hK hz.le).trans
      (by simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left hzK (mul_nonneg hK0.le hz.le))
  have hq : sqrt (mainNodes n:ℝ)≤K*z := by
    have H := sqrt_le_sqrt hq2
    simpa only [sqrt_sq (mul_nonneg hK0.le hz.le)] using H
  have ht : 8*(p:ℝ)*K*(a:ℝ)<ε*z := by
    have h : (8*(p:ℝ)*K*(a:ℝ))/ε < z := by
      apply lt_of_lt_of_le _ hzA
      dsimp [A]
      linarith
    have hh := (div_lt_iff₀ hε).mp h
    linarith only [hh]
  have hmain : (p:ℝ)*log (n:ℝ)*sqrt (mainNodes n:ℝ)*(a:ℝ)<ε*(n:ℝ) := by
    calc
      _ ≤ ((p:ℝ)*(8*z))*(K*z)*(a:ℝ) := by
        gcongr
        exact log_eighth _ hn'
      _ = (8*(p:ℝ)*K*(a:ℝ))*z^2 := by ring
      _ < (ε*z)*z^2 := mul_lt_mul_of_pos_right ht (by positivity)
      _ = ε*z^3 := by ring
      _ ≤ ε*z^8 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 (by decide)) hε.le
      _ = _ := by rw [eighth_pow (n:ℝ) hn'.le]
  have hd : (p:ℝ)*log (n:ℝ)*sqrt (mainNodes n:ℝ)<ε*(N:ℝ) := by
    apply (mul_lt_mul_iff_right₀ ha').mp
    have h := hmain.trans_le (mul_le_mul_of_nonneg_left hN' hε.le)
    linarith only [h]
  have H := exp_lt_exp.mpr ((lt_div_iff₀ (sqrt_pos.2 hQ')).mpr hd)
  rw [exp_nat_mul,exp_log hn'] at H
  exact H

#print axioms printed_polynomial_overhead_small
end P5MainBalance
