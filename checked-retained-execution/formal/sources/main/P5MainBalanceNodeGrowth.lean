import P5MainBalanceSize

/-! Printed MAIN node and width margins needed before comparing low
orders. No asymptotic assumption on the schedule is supplied by hand. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real Filter P5MainIterator

theorem printed_nodes_eventually_large (a : ℕ) :
    ∀ᶠ n : ℕ in atTop, a≤mainNodes n := by
  let Y := 128*(a:ℝ)*logEightBound+2
  have hc : 0<logEightBound := by
    have hlog2 : 0<log 2 := log_pos (by norm_num)
    unfold logEightBound
    positivity
  have hY : 2≤Y := by
    dsimp [Y]
    linarith only [show 0≤128*(a:ℝ)*logEightBound by positivity]
  have hY1 : 1≤Y := by linarith only [hY]
  filter_upwards [lambda_ge_along_sizes (Y^8)] with n hn
  let x := (mainLambda n:ℝ)
  let z := eighth x
  have hx : 1≤x := (one_le_pow₀ hY1).trans hn
  have hx' : 1<x := (by norm_num : (1:ℝ)<2^8).trans_le ((pow_le_pow_left₀ (by norm_num) hY 8).trans hn)
  have hYz : Y≤z := by
    rw [←eighth_pow_inverse Y (by linarith only [hY])]
    exact eighth_mono hn
  have hz1 : 1≤z := hY1.trans hYz
  have hz : 0≤z := by linarith only [hz1]
  have hν : (mainNu n:ℝ)≤logEightBound*z := ceil_logTwo_le x hx
  have hνp : 0<mainNu n := by
    have h := Nat.le_ceil (logTwo x)
    have hp : 0<logTwo x := div_pos (log_pos hx') (log_pos (by norm_num))
    exact_mod_cast hp.trans_le h
  unfold mainNodes
  apply (Nat.le_div_iff_mul_le (by omega : 0<128*mainNu n)).mpr
  have hh : (a:ℝ)*(128*(mainNu n:ℝ))≤x := by
    calc
      _ ≤ (a:ℝ)*(128*(logEightBound*z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hν (by norm_num)) (by positivity)
      _ = (128*(a:ℝ)*logEightBound)*z := by ring
      _ ≤ z*z := mul_le_mul_of_nonneg_right (by dsimp [Y] at hYz; linarith only [hYz]) hz
      _ = z^2 := by ring
      _ ≤ z^8 := pow_le_pow_right₀ hz1 (by decide)
      _ = x := eighth_pow x (by linarith only [hx])
  change (a:ℝ)*(128*(mainNu n:ℝ))≤(mainLambda n:ℝ) at hh
  exact_mod_cast hh

noncomputable def mainWidth (β n : ℕ) : ℕ :=
  (β+3)*⌈sqrt (mainLambda n:ℝ)⌉₊

theorem printed_tail_exponent (β n : ℕ) (hβ : 1≤β) (hQ : 0<mainNodes n) :
    256*(mainNu n:ℝ)≤(mainWidth β n:ℝ)^2/(8*(mainNodes n:ℝ)) := by
  have hQ' : 0<(mainNodes n:ℝ) := by exact_mod_cast hQ
  have hq : 128*mainNu n*mainNodes n≤mainLambda n := by
    unfold mainNodes
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  have hq' : 128*(mainNu n:ℝ)*(mainNodes n:ℝ)≤(mainLambda n:ℝ) := by exact_mod_cast hq
  have hβ' : (4:ℝ)≤(β:ℝ)+3 := by exact_mod_cast (by omega : 4≤β+3)
  have hW : 4*sqrt (mainLambda n:ℝ)≤(mainWidth β n:ℝ) := by
    unfold mainWidth
    push_cast
    exact mul_le_mul hβ' (Nat.le_ceil _) (sqrt_nonneg _) (by positivity)
  have hsq := pow_le_pow_left₀ (show 0≤4*sqrt (mainLambda n:ℝ) by positivity) hW 2
  rw [mul_pow,sq_sqrt (by positivity)] at hsq
  apply (le_div_iff₀ (by positivity)).mpr
  linarith only [hq',hsq]

#print axioms printed_nodes_eventually_large
#print axioms printed_tail_exponent
end P5MainBalance
