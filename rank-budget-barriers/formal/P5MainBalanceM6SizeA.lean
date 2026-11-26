import P5MainBalancePolyOverhead
import P5MainBalanceThinMeasure

/-! Numerical pieces of M.6 at the original r,Q,λ,ν, reducing
finite low-order budgets to fixed density and the actual retained
row count rather than arbitrary measurement or degree cost bounds. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

theorem printed_fast_condition (a : ℕ) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ n : ℕ in atTop, 2*(a:ℝ)≤ε*sqrt (mainNodes n:ℝ) := by
  let m := ⌈((2*(a:ℝ))/ε)^2⌉₊
  filter_upwards [printed_nodes_eventually_large m] with n hn
  have hn' : (m:ℝ)≤(mainNodes n:ℝ) := by exact_mod_cast hn
  have hm : ((2*(a:ℝ))/ε)^2≤(mainNodes n:ℝ) := (Nat.le_ceil _).trans hn'
  have hp := sqrt_le_sqrt hm
  rw [sqrt_sq (by positivity : 0≤2*(a:ℝ)/ε)] at hp
  have hp' := (div_le_iff₀ he).mp hp
  simpa only [mul_comm] using hp'

theorem printed_exponent_eventually_ge_two (a : ℕ) (ha : 0<a)
    (c : ℝ) (hc : 0<c) :
    ∀ᶠ n : ℕ in atTop,∀ N : ℕ,n≤a*N → 0<mainNodes n →
      2≤c*(N:ℝ)/sqrt (mainNodes n:ℝ) := by
  have hE := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (exp 2))
  filter_upwards [printed_polynomial_overhead_small a 1 ha c hc,hE] with n hn hnE
  intro N hN hQ
  have h₀ := hn N hN hQ
  rw [pow_one] at h₀
  exact exp_le_exp.mp (hnE.trans h₀.le)

theorem printed_small_measurement_error (C : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, 4*(C:ℝ)/(mainLambda n:ℝ)^3≤ε := by
  filter_upwards [lambda_ge_along_sizes (max 1 (4*(C:ℝ)/ε))] with n hn
  have hn1 : 1≤(mainLambda n:ℝ) := (le_max_left _ _).trans hn
  have hne : 0<(mainLambda n:ℝ) := by linarith only [hn1]
  have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hn)
  have hp := pow_le_pow_right₀ hn1 (show 1≤(3:ℕ) by decide)
  rw [pow_one] at hp
  apply (div_le_iff₀ (pow_pos hne _)).mpr
  exact hh.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp hε.le)

theorem printed_alphabet_le_sqrt (n : ℕ) (hν : 1≤mainNu n) :
    (mainAlphabet n:ℝ)≤sqrt (mainLambda n:ℝ) := by
  have h : (1:ℝ)≤mainNu n := by exact_mod_cast hν
  have hp : (1:ℝ)≤(mainNu n:ℝ)^2 := by nlinarith only [h,sq_nonneg ((mainNu n:ℝ)-1)]
  apply (Nat.floor_le (by positivity)).trans
  apply (div_le_iff₀ (by positivity : 0<(mainNu n:ℝ)^2)).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (sqrt_nonneg (mainLambda n:ℝ))

theorem printed_log_box_small (C n D : ℕ) (hn : 1≤n) (hD : D≤C*n)
    (hlarge : log (2*(C:ℝ)+1)≤(mainLambda n:ℝ)) :
    log (2*(D:ℝ)+1)≤2*(mainLambda n:ℝ) := by
  have hin : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hp : (D:ℝ)≤(C:ℝ)*(n:ℝ) := by exact_mod_cast hD
  have hmaj : 2*(D:ℝ)+1≤(2*(C:ℝ)+1)*(n:ℝ) := by
    nlinarith only [hin,mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤2 by norm_num)]
  have hlog := log_le_log (by positivity : 0<2*(D:ℝ)+1) hmaj
  rw [log_mul (by positivity) (by positivity)] at hlog
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hN : log (n:ℝ)≤(mainLambda n:ℝ)*log 2 :=
    (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have hL : 0≤(mainLambda n:ℝ) := by positivity
  have h2 : log 2≤1 := by
    have H := log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at H
    exact H
  have hnL : log (n:ℝ)≤(mainLambda n:ℝ) := hN.trans (by simpa using mul_le_mul_of_nonneg_left h2 hL)
  linarith only [hlog,hlarge,hnL]

theorem literal_small_tail_product (n : ℕ) (hL : 2≤mainLambda n) (hQ : 0<mainNodes n) :
    2*exp (-(mainWidth 1 n:ℝ)^2/(8*(mainNodes n:ℝ)))≤1/(mainLambda n:ℝ)^5 := by
  have h := printed_tail_exponent 1 n (by decide) hQ
  have hn := neg_le_neg h
  rw [←neg_div] at hn
  exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hn) (by norm_num)).trans (printed_tail_power n hL)

theorem literal_local_poly_by_n (n ell j N Q : ℕ) (ε : ℝ)
    (hn : 2≤n) (hN : N≤n) (hQ : 4≤Q)
    (he : ε≤1) (hl : ell≤n+1)
    (hj : (j:ℝ)*log (2*(Q:ℝ))≤ε*(N:ℝ)/sqrt (Q:ℝ)) :
    ell*(j+1)≤n^4 := by
  have hq : (4:ℝ)≤Q := by exact_mod_cast hQ
  have hqpos : 0<(Q:ℝ) := by linarith only [hq]
  have hs4 : sqrt (4:ℝ)=2 := by norm_num
  have hS : 2≤sqrt (Q:ℝ) := by rw [←hs4]; exact sqrt_le_sqrt hq
  have hTwo : (0:ℝ)<2*(Q:ℝ) := by positivity
  have hLog : (1/2:ℝ)≤log (2*(Q:ℝ)) := by
    have h := one_sub_inv_le_log_of_pos hTwo
    have ht : (2*(Q:ℝ))⁻¹≤(1/2:ℝ) := by
      rw [←one_div]
      apply (div_le_iff₀ hTwo).mpr
      linarith only [hq]
    linarith only [ht,h]
  have hProd : 1≤log (2*(Q:ℝ))*sqrt (Q:ℝ) := by
    have hh := mul_le_mul hLog hS (by norm_num : 0≤(2:ℝ)) (show 0≤log (2*(Q:ℝ)) by linarith)
    linarith only [hh]
  have hjN : (j:ℝ)≤(N:ℝ) := by
    calc
      _ ≤ (j:ℝ)*(log (2*(Q:ℝ))*sqrt (Q:ℝ)) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hProd (by positivity : 0≤(j:ℝ))
      _ = ((j:ℝ)*log (2*(Q:ℝ)))*sqrt (Q:ℝ) := by ring
      _ ≤ ε*(N:ℝ) := (le_div_iff₀ (sqrt_pos.2 hqpos)).mp hj
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (by positivity : 0≤(N:ℝ))
  have hJ : j≤N := by exact_mod_cast hjN
  exact (Nat.mul_le_mul hl (by omega : j+1≤n+1)).trans (by
    have hs : n+1≤n*n := by nlinarith only [show 2≤n from hn]
    simpa only [pow_succ,pow_zero,one_mul,Nat.mul_assoc] using Nat.mul_le_mul hs hs)

#print axioms printed_fast_condition
#print axioms printed_exponent_eventually_ge_two
#print axioms printed_small_measurement_error
#print axioms printed_alphabet_le_sqrt
#print axioms printed_log_box_small
#print axioms literal_small_tail_product
#print axioms literal_local_poly_by_n
end P5MainBalance.M6
