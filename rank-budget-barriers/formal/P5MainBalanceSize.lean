import P5MainBalanceSchedule
import MainIncidence

/-! The other finite hypothesis in M.4 is the graph thinning size
threshold. Derive it from the printed Q and constant cloned-size ratio. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real Filter

theorem eighth_pow_inverse (x : ℝ) (hx : 0≤x) : eighth (x^8)=x := by
  have h := eighth_pow (x^8) (by positivity)
  exact (pow_left_inj₀ (by unfold eighth; positivity) hx (by decide : (8:ℕ)≠0)).mp h

theorem printed_Qsquare_eventually_small (B : ℝ) (hB : 0≤B) :
    ∀ᶠ n : ℕ in atTop, B*(mainNodes n:ℝ)^2<(n:ℝ) := by
  let y := B*logEightBound^2+2
  have hy2 : 2≤y := by
    dsimp [y]
    linarith only [mul_nonneg hB (sq_nonneg logEightBound)]
  have hy : 1≤y := (by norm_num : (1:ℝ)≤2).trans hy2
  have hc : 0≤logEightBound := by
    have hp : 0<log 2 := log_pos (by norm_num)
    unfold logEightBound
    positivity
  have hEvent := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop (y^8))
  filter_upwards [hEvent] with n hn
  let z := eighth (n:ℝ)
  have hn1 : 1≤(n:ℝ) := (one_le_pow₀ hy).trans hn
  have hz : y≤z := by
    rw [←eighth_pow_inverse y (by linarith only [hy])]
    exact eighth_mono hn
  have hz1 := hy.trans hz
  have hz0 : 0≤z := by linarith only [hz1]
  have hql : (mainNodes n:ℝ)≤(mainLambda n:ℝ) := by
    unfold mainNodes
    exact_mod_cast Nat.div_le_self (mainLambda n) (128*mainNu n)
  have hν : (mainNodes n:ℝ)≤logEightBound*z := hql.trans (ceil_logTwo_le _ hn1)
  have hsq := pow_le_pow_left₀ (by positivity : 0≤(mainNodes n:ℝ)) hν 2
  have Bz : B*logEightBound^2<z := (show _<y from by dsimp [y]; linarith).trans_le hz
  calc
    _ ≤ B*(logEightBound*z)^2 := mul_le_mul_of_nonneg_left hsq hB
    _ = (B*logEightBound^2)*z^2 := by ring
    _ < z*z^2 := mul_lt_mul_of_pos_right Bz (by positivity)
    _ = z^3 := by ring
    _ ≤ z^8 := pow_le_pow_right₀ hz1 (by decide)
    _ = _ := eighth_pow _ (by positivity)

/-- The finite theorem's exact rational cutoff, eventually uniformly over
all layouts on the real printed dimensions (direct clone ratio 4 or 1). -/
theorem printed_thinning_threshold (a C : ℕ) (ha : 0<a)
    (γ : ℚ) (_hγ : 0<γ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n≤a*N →
      7776*(mainNodes n:ℚ)*(4*C*(mainNodes n:ℚ))/
        (FiniteGrowth.coefficient γ (1/4))^2 < (N:ℚ) := by
  let B : ℚ := 7776*(4*C:ℚ)/(FiniteGrowth.coefficient γ (1/4))^2
  have hB : 0≤B := by unfold B; positivity
  have hA : 0<(a:ℝ) := by exact_mod_cast ha
  have hBr : 0≤(B:ℝ) := by exact_mod_cast hB
  filter_upwards [printed_Qsquare_eventually_small ((a:ℝ)*(B:ℝ)) (by positivity)] with n hn
  intro N hN
  have hNR : (n:ℝ)≤(a:ℝ)*(N:ℝ) := by exact_mod_cast hN
  have hf : (B:ℝ)*(mainNodes n:ℝ)^2<(N:ℝ) := by
    apply (mul_lt_mul_iff_right₀ hA).mp
    have H := hn.trans_le hNR
    linarith only [H]
  have hf' : B*(mainNodes n:ℚ)^2<(N:ℚ) := by exact_mod_cast hf
  convert hf' using 1
  unfold B
  ring

#print axioms eighth_pow_inverse
#print axioms printed_Qsquare_eventually_small
#print axioms printed_thinning_threshold
end P5MainBalance
