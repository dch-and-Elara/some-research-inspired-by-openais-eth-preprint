import P5MainIteratorChoose
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-! The actual printed alphabet, not a free balanced-layout assumption.
The core source uses λ=ceil(log₂ n), ν=ceil(log₂ λ), and floors its
sqrt-log alphabet. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Filter Real P5MainIterator

noncomputable def mainLambda (n : ℕ) : ℕ := ⌈logTwo (n:ℝ)⌉₊
noncomputable def mainNu (n : ℕ) : ℕ := ⌈logTwo (mainLambda n:ℝ)⌉₊
noncomputable def mainAlphabet (n : ℕ) : ℕ :=
  ⌊sqrt (mainLambda n:ℝ) / ((mainNu n:ℝ)^2)⌋₊
noncomputable def mainNodes (n : ℕ) : ℕ :=
  mainLambda n/(128*mainNu n)

noncomputable def eighth (x : ℝ) := sqrt (sqrt (sqrt x))
noncomputable def logEightBound : ℝ := 8/(log 2)+1

theorem eighth_pow (x : ℝ) (hx : 0≤x) : eighth x ^8=x := by
  rw [show eighth x ^8=((eighth x ^2)^2)^2 by ring]
  unfold eighth
  rw [sq_sqrt (sqrt_nonneg _),sq_sqrt (sqrt_nonneg _),sq_sqrt hx]

theorem eighth_mono : Monotone eighth := fun _ _ h => sqrt_le_sqrt (sqrt_le_sqrt (sqrt_le_sqrt h))

theorem log_eighth (x : ℝ) (hx : 0<x) : log x≤8*eighth x := by
  have he : 0<eighth x := by unfold eighth; positivity
  have h := log_le_sub_one_of_pos he
  unfold eighth at h
  rw [log_sqrt (sqrt_nonneg _),log_sqrt (sqrt_nonneg _),log_sqrt hx.le] at h
  unfold eighth
  linarith only [h]

theorem ceil_logTwo_le (x : ℝ) (hx : 1≤x) :
    ((⌈logTwo x⌉₊:ℕ):ℝ)≤logEightBound*eighth x := by
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hX : 0<x := by linarith only [hx]
  have hN : 0≤logTwo x := div_nonneg (log_nonneg hx) hlog2.le
  have hA := Nat.ceil_lt_add_one hN
  have hB : (1:ℝ)≤eighth x := by
    have H := eighth_mono hx
    have hs : eighth 1=1 := by norm_num [eighth]
    simpa only [hs] using H
  have hC : logTwo x≤(8/log 2)*eighth x := by
    unfold logTwo
    calc
      _ ≤ (8*eighth x)/log 2 := div_le_div_of_nonneg_right (log_eighth x hX) hlog2.le
      _ = _ := by ring
  unfold logEightBound
  linarith only [hA,hB,hC]

theorem lambda_ge_along_sizes (X : ℝ) :
    ∀ᶠ n : ℕ in atTop, X≤(mainLambda n:ℝ) := by
  have ht : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := ht.eventually (eventually_ge_atTop (X*log 2))
  filter_upwards [h] with n hn
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hh : X≤logTwo (n:ℝ) := (le_div_iff₀ hlog2).mpr hn
  exact hh.trans (Nat.le_ceil _)

set_option maxHeartbeats 6200000 in
theorem printed_alphabet_eventually_large (a : ℕ) :
    ∀ᶠ n : ℕ in atTop, a≤mainAlphabet n := by
  let y := (a:ℝ)*logEightBound^2+2
  have hc : 0<logEightBound := by
    have hlog2 : 0<log 2 := log_pos (by norm_num)
    unfold logEightBound
    positivity
  have hy2 : 2≤y := by
    dsimp [y]
    linarith only [mul_nonneg (show 0≤(a:ℝ) by positivity) (sq_nonneg logEightBound)]
  have hy : 1≤y := (by norm_num : (1:ℝ)≤2).trans hy2
  have hy0 : 0≤y := by linarith only [hy]
  filter_upwards [lambda_ge_along_sizes (y^8)] with n hn
  let x := (mainLambda n:ℝ)
  let z := eighth x
  have hx : 1≤x := (one_le_pow₀ hy).trans hn
  have hyz : y≤z := by
    have hs : (eighth (y^8))^8=y^8 := eighth_pow _ (by positivity)
    have hh : eighth (y^8)=y := by
      apply (pow_left_inj₀ _ hy0 (by decide : (8:ℕ)≠0)).mp hs
      unfold eighth
      positivity
    rw [←hh]
    exact eighth_mono hn
  have hz0 : 0≤z := by dsimp [z,eighth]; positivity
  have hz1 : 1≤z := hy.trans hyz
  have hg : (a:ℝ)*logEightBound^2≤z^2 := by
    calc
      _ ≤ y := by dsimp [y]; linarith
      _ ≤ z := hyz
      _ ≤ z^2 := by simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left hz1 hz0
  have hν : (mainNu n:ℝ)≤logEightBound*z := ceil_logTwo_le x hx
  have hs : sqrt x=z^4 := by
    dsimp [z,eighth]
    rw [show (sqrt (sqrt (sqrt x)))^4=((sqrt (sqrt (sqrt x)))^2)^2 by ring]
    rw [sq_sqrt (sqrt_nonneg _),sq_sqrt (sqrt_nonneg _)]
  by_cases hv : mainNu n=0
  · have hlog := Nat.le_ceil (logTwo x)
    have hx' : 1<x := by
      exact (by norm_num : (1:ℝ)<2^8).trans_le ((pow_le_pow_left₀ (by norm_num) hy2 8).trans hn)
    have hp : 0<logTwo x := div_pos (log_pos hx') (log_pos (by norm_num))
    change logTwo x≤(mainNu n:ℝ) at hlog
    rw [hv,Nat.cast_zero] at hlog
    linarith only [hlog,hp]
  have hv' : 0<(mainNu n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hv
  unfold mainAlphabet
  apply Nat.le_floor
  apply (le_div_iff₀ (sq_pos_of_pos hv')).mpr
  have hsq := pow_le_pow_left₀ (show 0≤(mainNu n:ℝ) by positivity) hν 2
  calc
    _ ≤ (a:ℝ)*(logEightBound*z)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = ((a:ℝ)*logEightBound^2)*z^2 := by ring
    _ ≤ z^2*z^2 := mul_le_mul_of_nonneg_right hg (sq_nonneg _)
    _ = _ := by rw [hs]; ring

theorem printed_balance_threshold (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, 4*C≤3*mainAlphabet n := by
  filter_upwards [printed_alphabet_eventually_large (4*C)] with n hn
  omega

#print axioms eighth_pow
#print axioms ceil_logTwo_le
#print axioms lambda_ge_along_sizes
#print axioms printed_alphabet_eventually_large
#print axioms printed_balance_threshold
end P5MainBalance
