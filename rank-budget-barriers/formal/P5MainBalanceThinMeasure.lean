import P5MainBalanceSchedule

/-! The actual M.6 measurement budget uses the exceptional row tail
before the looser layout certificate discards it. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real P5MainIterator

theorem exact_tail_power (lambda nu : ℕ) (hLambda : 2≤lambda)
    (hν : logTwo (lambda:ℝ)≤(nu:ℝ)) :
    2*exp (-(256*(nu:ℝ)))≤1/(lambda:ℝ)^5 := by
  have hp : 0<(lambda:ℝ) := by exact_mod_cast (by omega : 0<lambda)
  have hLambda2 : (2:ℝ)≤lambda := by exact_mod_cast hLambda
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hlog1 : log 2≤1 := by have H:=log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num); norm_num at H; exact H
  have hL : log (lambda:ℝ)≤(nu:ℝ)*log 2 := (div_le_iff₀ hlog2).mp hν
  have hL' := log_le_log (by norm_num : (0:ℝ)<2) hLambda2
  have H := mul_le_mul_of_nonneg_left hlog1 (show 0≤(nu:ℝ) by positivity)
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by norm_num) (exp_ne_zero _),log_exp,one_div,log_inv,log_pow]
  norm_num only [Nat.cast_ofNat]
  have hN : log (lambda:ℝ)≤(nu:ℝ) := hL.trans (by simpa only [mul_one] using H)
  linarith only [hL',hN,(show 0≤(nu:ℝ) by positivity)]

theorem printed_tail_power (n : ℕ) (hLambda : 2≤mainLambda n) :
    2*exp (-(256*(mainNu n:ℝ)))≤1/(mainLambda n:ℝ)^5 :=
  exact_tail_power (mainLambda n) (mainNu n) hLambda (Nat.le_ceil _)

/-- Retained true row dimensions and exact (2D+1)-ary tuple box. -/
theorem literal_measurement_small (M N r H D lambda Q b : ℕ) (ε δ : ℝ)
    (hLambda : 1≤lambda) (hQ : Q≤lambda) (hQp : 0<Q)
    (hr : (r:ℝ)≤sqrt (lambda:ℝ)) (hM : M≤b*N)
    (hCoord : (r:ℝ)*(H:ℝ)≤2*(M:ℝ)*(r:ℝ)*δ)
    (hδ : δ≤1/(lambda:ℝ)^5)
    (hD : log (2*(D:ℝ)+1)≤2*(lambda:ℝ))
    (hErr : 4*(b:ℝ)/(lambda:ℝ)^3≤ε) :
    log (((2*D+1)^(r*H):ℕ):ℝ)≤ε*(N:ℝ)/sqrt (Q:ℝ) := by
  have hl : 0<(lambda:ℝ) := by exact_mod_cast (by omega : 0<lambda)
  have hp : 0<sqrt (lambda:ℝ) := sqrt_pos.2 hl
  have hq : 0<(Q:ℝ) := by exact_mod_cast hQp
  have hq' : 0<sqrt (Q:ℝ) := sqrt_pos.2 hq
  have hs : sqrt (Q:ℝ)≤sqrt (lambda:ℝ) :=
    sqrt_le_sqrt (by exact_mod_cast hQ)
  have hN : (M:ℝ)≤(b:ℝ)*(N:ℝ) := by exact_mod_cast hM
  have hLog0 : 0≤log (2*(D:ℝ)+1) :=
    log_nonneg (by exact_mod_cast (by omega : 1≤2*D+1))
  push_cast
  rw [log_pow,Nat.cast_mul]
  apply (le_div_iff₀ hq').mpr
  calc
    _ ≤ ((r:ℝ)*(H:ℝ))*log (2*(D:ℝ)+1)*sqrt (lambda:ℝ) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (2*(M:ℝ)*(r:ℝ)*δ)*log (2*(D:ℝ)+1)*sqrt (lambda:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoord hLog0) hp.le
    _ ≤ (2*(M:ℝ)*(r:ℝ)*(1/(lambda:ℝ)^5))*log (2*(D:ℝ)+1)*sqrt (lambda:ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ (by positivity)) hLog0) hp.le
    _ ≤ (2*(M:ℝ)*sqrt (lambda:ℝ)*(1/(lambda:ℝ)^5))*(2*(lambda:ℝ))*sqrt (lambda:ℝ) := by
      gcongr
    _ = 4*(M:ℝ)/(lambda:ℝ)^3 := by
      have h := sq_sqrt hl.le
      field_simp
      nlinarith only [h]
    _ ≤ (4*(b:ℝ)/(lambda:ℝ)^3)*(N:ℝ) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN (show 0≤(4:ℝ) by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_right hErr (by positivity)

#print axioms exact_tail_power
#print axioms printed_tail_power
#print axioms literal_measurement_small
end P5MainBalance
