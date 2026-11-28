import P5MainBalanceM6Mix
import P5MainBalanceM6PrintedSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000

/-! Numerical side of the printed interval, independently of a fixed
layout. The general fixed-beta schedule and every finite valid
(2<=r,1<=R,6R<=Q) schedule both retain the weight-zero row. -/
namespace V8NativeMessage.N6.MainFiber
open P5MainBalance P5MainBalance.M6 P5MainIterator Real Filter
open scoped BigOperators Classical

noncomputable section

def startValue (r Q R : ℕ) : ℝ :=
  (Q:ℝ)*((r:ℝ)-1)/(2*(r:ℝ))-((R:ℝ)-1)/2

def intervalStart (r Q R : ℕ) : ℕ := ⌊startValue r Q R⌋₊

theorem interval_start_positive (r Q R : ℕ) (hr : 2≤r) (hR : 1≤R)
    (hfit : 6*R≤Q) :
    0< intervalStart r Q R ∧ (intervalStart r Q R:ℤ)=⌊startValue r Q R⌋ := by
  have hr' : (2:ℝ)≤r := by exact_mod_cast hr
  have hR' : (1:ℝ)≤R := by exact_mod_cast hR
  have hfit' : 6*(R:ℝ)≤Q := by exact_mod_cast hfit
  have hl : (Q:ℝ)/4≤(Q:ℝ)*((r:ℝ)-1)/(2*(r:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [mul_nonneg (show 0≤(r:ℝ)-2 by linarith only [hr'])
      (show 0≤(Q:ℝ) by positivity)]
  have hA : 1≤startValue r Q R := by
    unfold startValue
    linarith only [hl,hfit',hR']
  have hfloor : 1 ≤ intervalStart r Q R := Nat.le_floor (by simpa only [Nat.cast_one] using hA)
  exact ⟨hfloor,Int.natCast_floor_eq_floor (by linarith only [hA])⟩

theorem zero_is_printed_exceptional (r Q R : ℕ) (hr : 2≤r) (hR : 1≤R)
    (hfit : 6*R≤Q) :
    outsideInterval (intervalStart r Q R) R 0 := by
  rintro ⟨h, _⟩
  exact (Nat.not_le_of_gt (interval_start_positive r Q R hr hR hfit).1) h

theorem fixed_beta_published_range (β : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2≤mainAlphabet n ∧ 32≤mainWidth β n ∧ 6*mainWidth β n≤mainNodes n := by
  let c : ℝ := 6*2*(β+3)*128*logEightBound
  have hc : 0≤c := by
    dsimp [c,logEightBound]
    positivity
  let K : ℝ := c+32
  have hK32 : 32≤K := by dsimp only [K]; linarith only [hc]
  have hK1 : 1≤K := by linarith only [hK32]
  filter_upwards [lambda_ge_along_sizes (K^8),printed_alphabet_eventually_large 2] with n hn hr
  let x := (mainLambda n:ℝ)
  let z := eighth x
  have hx₁ : 1≤x := (one_le_pow₀ hK1).trans hn
  have hz : K≤z := by
    rw [←eighth_pow_inverse K (by linarith only [hK32])]
    exact eighth_mono hn
  have hz32 : 32≤z := hK32.trans hz
  have hz1 : 1≤z := by linarith only [hz32]
  have hν : (mainNu n:ℝ)≤logEightBound*z := ceil_logTwo_le x hx₁
  have hx2 : 1<x := by
    exact (by norm_num : (1:ℝ)<2^8).trans_le
      ((pow_le_pow_left₀ (by norm_num) (show 2≤K by linarith only [hK32]) 8).trans hn)
  have hνp : 0<mainNu n := by
    have hlog : 0<logTwo x := div_pos (log_pos hx2) (log_pos (by norm_num))
    exact_mod_cast hlog.trans_le (Nat.le_ceil _)
  have hs : sqrt x=z^4 := by
    dsimp [z,eighth]
    rw [show (sqrt (sqrt (sqrt x)))^4=((sqrt (sqrt (sqrt x)))^2)^2 by ring]
    rw [sq_sqrt (sqrt_nonneg _),sq_sqrt (sqrt_nonneg _)]
  have hs1 : 1≤z^4 := one_le_pow₀ hz1
  have hs32 : 32≤sqrt x := by
    rw [hs]
    have hp := pow_le_pow_right₀ hz1 (show 1≤(4:ℕ) by decide)
    rw [pow_one] at hp
    exact hz32.trans hp
  have hRH : (mainWidth β n:ℝ)≤2*(β+3)*z^4 := by
    have hceil := Nat.ceil_lt_add_one (sqrt_nonneg x)
    change ((⌈sqrt x⌉₊:ℕ):ℝ)<sqrt x+1 at hceil
    unfold mainWidth
    push_cast
    change ((β:ℝ)+3)*((⌈sqrt x⌉₊:ℕ):ℝ)≤2*((β:ℝ)+3)*z^4
    rw [hs] at hceil
    have hce : ((⌈sqrt x⌉₊:ℕ):ℝ)≤2*z^4 := by
      rw [hs]
      linarith only [hceil,hs1]
    calc
      _ ≤ ((β:ℝ)+3)*(2*z^4) := mul_le_mul_of_nonneg_left hce (by positivity)
      _ = _ := by ring
  refine ⟨hr,?_,?_⟩
  · have hceil : (32:ℝ)≤(⌈sqrt (mainLambda n:ℝ)⌉₊:ℕ) := hs32.trans (Nat.le_ceil _)
    have hce : 32≤⌈sqrt (mainLambda n:ℝ)⌉₊ := by exact_mod_cast hceil
    unfold mainWidth
    exact hce.trans (Nat.le_mul_of_pos_left _ (by omega))
  · unfold mainNodes
    apply (Nat.le_div_iff_mul_le (by omega : 0<128*mainNu n)).mpr
    have H : 6*(mainWidth β n:ℝ)*(128*(mainNu n:ℝ))≤x := by
      calc
        _ ≤ 6*(2*(β+3)*z^4)*(128*(logEightBound*z)) := by gcongr
        _ = c*z^5 := by dsimp [c]; ring
        _ ≤ z*z^5 :=
          mul_le_mul_of_nonneg_right (by dsimp [K] at hz; linarith only [hz]) (by positivity)
        _ = z^6 := by ring
        _ ≤ z^8 := pow_le_pow_right₀ hz1 (by decide)
        _ = x := eighth_pow _ (by linarith only [hx₁])
    change 6*(mainWidth β n:ℝ)*(128*(mainNu n:ℝ))≤(mainLambda n:ℝ) at H
    exact_mod_cast H

theorem fixed_beta_eventually_zero_exceptional (β : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      outsideInterval (intervalStart (mainAlphabet n) (mainNodes n) (mainWidth β n))
        (mainWidth β n) 0 := by
  filter_upwards [fixed_beta_published_range β] with n h
  exact zero_is_printed_exceptional _ _ _ h.1 (by omega) h.2.2

#print axioms interval_start_positive
#print axioms zero_is_printed_exceptional
#print axioms fixed_beta_published_range
#print axioms fixed_beta_eventually_zero_exceptional
end
end V8NativeMessage.N6.MainFiber
