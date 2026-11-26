import P5MainBalanceM6PrintedSize

/-! The printed interval and interpolation nodes used by the MAIN source. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

noncomputable def nativeGrid (n : ℕ) (i : Fin (mainNodes n)) : ℚ := (i.val:ℚ)+1

theorem nativeGrid_inj (n : ℕ) : Function.Injective (nativeGrid n) := by
  intro i j h
  unfold nativeGrid at h
  apply Fin.ext
  exact_mod_cast (add_right_cancel h : (i.val:ℚ)=(j.val:ℚ))

theorem nativeGrid_nonzero (n : ℕ) (i : Fin (mainNodes n)) : nativeGrid n i≠0 := by
  unfold nativeGrid
  positivity

noncomputable def printedMean (n : ℕ) : ℝ :=
  (mainNodes n:ℝ)*((mainAlphabet n:ℝ)-1)/(2*(mainAlphabet n:ℝ))

noncomputable def printedStart (n : ℕ) : ℕ :=
  ⌊printedMean n-((mainWidth 1 n:ℝ)-1)/2⌋₊

theorem printed_mean_range (n : ℕ) (hr : 2≤mainAlphabet n) :
    (mainNodes n:ℝ)/4≤printedMean n ∧ printedMean n≤(mainNodes n:ℝ)/2 := by
  have h : (2:ℝ)≤mainAlphabet n := by exact_mod_cast hr
  have hR : 0<(mainAlphabet n:ℝ) := by linarith only [h]
  have hQ := show 0≤(mainNodes n:ℝ) by positivity
  unfold printedMean
  constructor
  · apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [h,hQ,mul_nonneg (show 0≤(mainAlphabet n:ℝ)-2 by linarith) hQ]
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [h,hQ]

set_option maxHeartbeats 8000000 in
theorem printed_width_interval_eventually :
    ∀ᶠ n : ℕ in atTop,32≤mainWidth 1 n ∧ 6*mainWidth 1 n≤mainNodes n := by
  let K := 6*8*128*logEightBound+8
  have hK8 : 8≤K := by
    dsimp [K,logEightBound]
    linarith only [show 0≤8/log 2 by positivity]
  have hK1 : 1≤K := by linarith only [hK8]
  filter_upwards [lambda_ge_along_sizes (K^8)] with n hn
  let x := (mainLambda n:ℝ)
  let z := eighth x
  have hx₁ : 1≤x := (one_le_pow₀ hK1).trans hn
  have hz : K≤z := by
    rw [←eighth_pow_inverse K (by linarith only [hK8])]
    exact eighth_mono hn
  have hZ8 : 8≤z := hK8.trans hz
  have hZ1 : 1≤z := by linarith only [hZ8]
  have hZ0 : 0≤z := by linarith only [hZ8]
  have hν : (mainNu n:ℝ)≤logEightBound*z := ceil_logTwo_le x hx₁
  have hx2 : 1<x := by
    exact (by norm_num : (1:ℝ)<8^8).trans_le ((pow_le_pow_left₀ (by norm_num) hK8 8).trans hn)
  have hνp : 0<mainNu n := by
    have hLog := show 0<logTwo x from div_pos (log_pos hx2) (log_pos (by norm_num))
    exact_mod_cast hLog.trans_le (Nat.le_ceil _)
  have hs : sqrt x=z^4 := by
    dsimp [z,eighth]
    rw [show (sqrt (sqrt (sqrt x)))^4=((sqrt (sqrt (sqrt x)))^2)^2 by ring]
    rw [sq_sqrt (sqrt_nonneg _),sq_sqrt (sqrt_nonneg _)]
  have hs1 : 1≤z^4 := one_le_pow₀ hZ1
  have hRLo : 8≤sqrt x := by
    rw [hs]
    have h4 := pow_le_pow_right₀ hZ1 (show 1≤(4:ℕ) by decide)
    rw [pow_one] at h4
    exact hZ8.trans h4
  have hRH : (mainWidth 1 n:ℝ)≤8*z^4 := by
    unfold mainWidth
    push_cast
    have h₂ := Nat.ceil_lt_add_one (sqrt_nonneg x)
    change ((⌈sqrt x⌉₊:ℕ):ℝ)<sqrt x+1 at h₂
    rw [hs] at h₂
    change 4*((⌈sqrt x⌉₊:ℕ):ℝ)≤8*z^4
    rw [hs]
    linarith only [h₂,hs1]
  constructor
  · have hceil : (8:ℝ)≤(⌈sqrt (mainLambda n:ℝ)⌉₊:ℕ) := hRLo.trans (Nat.le_ceil _)
    have hce : 8≤⌈sqrt (mainLambda n:ℝ)⌉₊ := by exact_mod_cast hceil
    unfold mainWidth
    omega
  · unfold mainNodes
    apply (Nat.le_div_iff_mul_le (by omega : 0<128*mainNu n)).mpr
    have H : 6*(mainWidth 1 n:ℝ)*(128*(mainNu n:ℝ))≤x := by
      calc
        _ ≤ 6*(8*z^4)*(128*(logEightBound*z)) := by gcongr
        _ = (6*8*128*logEightBound)*z^5 := by ring
        _ ≤ z*z^5 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [K] at hz
          linarith only [hz]
        _ = z^6 := by ring
        _ ≤ z^8 := pow_le_pow_right₀ hZ1 (by decide)
        _ = x := eighth_pow _ (by linarith only [hx₁])
    change 6*(mainWidth 1 n:ℝ)*(128*(mainNu n:ℝ))≤(mainLambda n:ℝ) at H
    exact_mod_cast H

theorem printed_start_floor_exact (n : ℕ) (hr : 2≤mainAlphabet n)
    (hR : 6*mainWidth 1 n≤mainNodes n) :
    (printedStart n:ℤ)=⌊printedMean n-((mainWidth 1 n:ℝ)-1)/2⌋ := by
  have hb := (printed_mean_range n hr).1
  have hR' : 6*(mainWidth 1 n:ℝ)≤(mainNodes n:ℝ) := by exact_mod_cast hR
  have hor : 0≤printedMean n-((mainWidth 1 n:ℝ)-1)/2 := by
    linarith only [hb,hR',show 0≤(mainWidth 1 n:ℝ) by positivity]
  exact Int.natCast_floor_eq_floor hor

#print axioms nativeGrid_inj
#print axioms nativeGrid_nonzero
#print axioms printed_mean_range
#print axioms printed_width_interval_eventually
#print axioms printed_start_floor_exact
end P5MainBalance.M6
