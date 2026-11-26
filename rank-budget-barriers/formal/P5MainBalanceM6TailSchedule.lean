import P5MainBalanceM6PrintedSchedule
import P5MainBalanceM6Mix

/-! Numerical bridge using the literal floor interval and schedule.
A weaker elementary tail constant still beats lambda^-5. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

theorem printed_interval_tail_deviation (n j : ℕ)
    (hr : 2≤mainAlphabet n) (hR : 32≤mainWidth 1 n)
    (hQR : 6*mainWidth 1 n≤mainNodes n)
    (hOut : outsideInterval (printedStart n) (mainWidth 1 n) j) :
    (mainWidth 1 n:ℝ)/4≤|(j:ℝ)-printedMean n| := by
  let A := printedStart n
  let R := mainWidth 1 n
  let mu := printedMean n
  have hloor := printed_start_floor_exact n hr hQR
  change (A:ℤ)=⌊mu-((R:ℝ)-1)/2⌋ at hloor
  have hLow : (A:ℝ)≤mu-((R:ℝ)-1)/2 := by
    have h := Int.floor_le (mu-((R:ℝ)-1)/2)
    rwa [←hloor,Int.cast_natCast] at h
  have hHi : mu-((R:ℝ)-1)/2<(A:ℝ)+1 := by
    have h := Int.lt_floor_add_one (mu-((R:ℝ)-1)/2)
    rwa [←hloor,Int.cast_natCast] at h
  have hR' : (32:ℝ)≤R := by exact_mod_cast hR
  change (R:ℝ)/4≤|((j:ℝ)-mu)|
  unfold outsideInterval at hOut
  change ¬(A≤j ∧ j<A+R) at hOut
  by_cases h : A≤j
  · have hn : A+R≤j := by omega
    have hn' : (A:ℝ)+(R:ℝ)≤j := by exact_mod_cast hn
    apply le_trans _ (le_abs_self _)
    linarith only [hHi,hR',hn']
  · have hn : (j:ℝ)≤A := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    apply le_trans _ (neg_le_abs _)
    linarith only [hLow,hR',hn]

theorem printed_exponent_room (n : ℕ) (hQ : 0<mainNodes n) :
    32*(mainNu n:ℝ)≤(mainWidth 1 n:ℝ)^2/(64*(mainNodes n:ℝ)) := by
  calc
    _ = (256*(mainNu n:ℝ))/8 := by ring
    _ ≤ ((mainWidth 1 n:ℝ)^2/(8*(mainNodes n:ℝ)))/8 :=
      div_le_div_of_nonneg_right (printed_tail_exponent 1 n (by decide) hQ) (by norm_num)
    _ = _ := by ring

theorem elementary_tail_power (lambda nu : ℕ) (hLambda : 2≤lambda)
    (hNu : logTwo (lambda:ℝ)≤(nu:ℝ)) :
    2*exp (-(32*(nu:ℝ)))≤1/(lambda:ℝ)^5 := by
  have hp : 0<(lambda:ℝ) := by exact_mod_cast (by omega : 0<lambda)
  have hLambda2 : (2:ℝ)≤lambda := by exact_mod_cast hLambda
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hlog1 : log 2≤1 := by have H:=log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num); norm_num at H; exact H
  have hL : log (lambda:ℝ)≤(nu:ℝ)*log 2 := (div_le_iff₀ hlog2).mp hNu
  have hL' := log_le_log (by norm_num : (0:ℝ)<2) hLambda2
  have H := mul_le_mul_of_nonneg_left hlog1 (show 0≤(nu:ℝ) by positivity)
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by norm_num) (exp_ne_zero _),log_exp,one_div,log_inv,log_pow]
  norm_num only [Nat.cast_ofNat]
  have hN : log (lambda:ℝ)≤(nu:ℝ) := hL.trans (by simpa only [mul_one] using H)
  linarith only [hL',hN,(show 0≤(nu:ℝ) by positivity)]

theorem printed_R_tail_power (n : ℕ) (hLam : 2≤mainLambda n) (hQ : 0<mainNodes n) :
    2*exp (-(mainWidth 1 n:ℝ)^2/(64*(mainNodes n:ℝ)))≤1/(mainLambda n:ℝ)^5 := by
  have h := printed_exponent_room n hQ
  have hh : -(mainWidth 1 n:ℝ)^2/(64*(mainNodes n:ℝ)) ≤ -(32*(mainNu n:ℝ)) := by
    rw [neg_div]
    exact neg_le_neg h
  exact (mul_le_mul_of_nonneg_left (exp_le_exp_of_le hh) (by norm_num)).trans
    (elementary_tail_power (mainLambda n) (mainNu n) hLam (Nat.le_ceil _))

#print axioms printed_interval_tail_deviation
#print axioms printed_exponent_room
#print axioms elementary_tail_power
#print axioms printed_R_tail_power
end P5MainBalance.M6
