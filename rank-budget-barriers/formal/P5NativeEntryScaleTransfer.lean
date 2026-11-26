import P5NativeEntryTrace
import P5NativeEntrySparsify

/-! Conversion of the exact rounded printed scale to the unrounded
logarithmic exponent in the paper. -/
namespace Paper5.NativeEntry
open Real Filter
open scoped Topology

theorem log_source_lambda_bounds {n : ℕ} (hn : 2≤n) :
    1≤logb 2 (n:ℝ) ∧
    logb 2 (n:ℝ)≤(sourceLambda n:ℝ) ∧ (sourceLambda n:ℝ)≤logb 2 (n:ℝ)+1 := by
  have h : 1≤logb 2 (n:ℝ) := by
    have he := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤n by exact_mod_cast hn)
    simpa using he
  rw [source_lambda_literal]
  exact ⟨h,Nat.le_ceil _, (Nat.ceil_lt_add_one (by linarith only [h])).le⟩

theorem rounded_le_nine_binary {n : ℕ} (hn : 4≤n) :
    roundedScale n≤9*binaryScale n := by
  let x := logb 2 (n:ℝ)
  let l := logb 2 x
  have hx2 : 2≤x := by
    have hm := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<4) (show (4:ℝ)≤n by exact_mod_cast hn)
    have hq : logb 2 (4:ℝ)=2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.logb_pow]
      simp
    exact hq ▸ hm
  have hx : 0<x := by linarith only [hx2]
  have hl : 1≤l := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) hx2
    simpa [l] using h
  obtain ⟨_,hLa,hLb⟩ := log_source_lambda_bounds (n:=n) (by omega)
  change x≤(sourceLambda n:ℝ) at hLa
  change (sourceLambda n:ℝ)≤x+1 at hLb
  have hLpos : 0<(sourceLambda n:ℝ) := hx.trans_le hLa
  have hNu : (sourceNu n:ℝ)≤3*l := by
    rw [source_nu_literal]
    have he : logb 2 (2*x)=1+l := by
      rw [Real.logb_mul (by norm_num) hx.ne']
      simp [l]
    have hb := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hLpos
      (show (sourceLambda n:ℝ)≤2*x by linarith only [hLb,hx2])
    rw [he] at hb
    have hp : 0≤logb 2 (sourceLambda n:ℝ) :=
      Real.logb_nonneg (by norm_num) (by linarith only [hLa,hx2])
    have hce := Nat.ceil_lt_add_one hp
    linarith only [hl,hb,hce]
  have ht : (n:ℝ)*(sourceNu n:ℝ)^2≤(n:ℝ)*(3*l)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNu 2) (by positivity)
  change (n:ℝ)*(sourceNu n:ℝ)^2/sqrt (sourceLambda n:ℝ)≤9*((n:ℝ)*l^2/sqrt x)
  calc
    _ ≤ (n:ℝ)*(3*l)^2/sqrt (sourceLambda n:ℝ) :=
      div_le_div_of_nonneg_right ht (sqrt_nonneg _)
    _ ≤ (n:ℝ)*(3*l)^2/sqrt x :=
      div_le_div_of_nonneg_left (by positivity) (sqrt_pos.mpr hx) (sqrt_le_sqrt hLa)
    _ = _ := by ring

theorem binary_half_comparison {d n : ℕ} (hD : 4≤d) (hd : d≤n) (hn : n≤2*d) :
    binaryScale n≤144*binaryScale d := by
  have h₁ := binary_le_two_rounded (n:=n) (by omega)
  have h₂ := rounded_half_comparison (d:=d) (n:=n) (by omega) hd hn
  have h₃ := rounded_le_nine_binary hD
  linarith only [h₁,h₂,h₃]

theorem preliminary_eventual_unclipped :
    ∃ n₀ : ℕ, ∀ n≥n₀, binaryScale n≤2*(n:ℝ) := by
  obtain ⟨n₀,h⟩ := eventual_prelim_guard
  refine ⟨max 2 n₀,fun n hn=>?_⟩
  have h₁ : 2≤n := (le_max_left _ _).trans hn
  have h₂ : n₀≤n := (le_max_right _ _).trans hn
  have h₃ := h n h₂
  have hb := binary_le_two_rounded h₁
  have hq := unclipped_scale_le h₁ (by omega : 0<printedGroups n)
  linarith only [hb,hq]

theorem rational_entry_eventual_cost :
    ∃ n₀ : ℕ, ∀ n≥n₀,∀ (sgn : Fin n→Bool) (T : ℕ),
      RationalEntryReceipt sgn T → binaryScale n/16≤P5MainIterator.logTwo T := by
  obtain ⟨n₀,h⟩ := preliminary_eventual_unclipped
  refine ⟨max 20 n₀,?_⟩
  intro n hn sgn T W
  have h₂ := h n ((le_max_right _ _).trans hn)
  have h₁ := rational_entry_reached_paid ((le_max_left _ _).trans hn) W
  rw [min_eq_right (by linarith only [h₂,show (0:ℝ)≤n by positivity])] at h₁
  exact h₁

#print axioms log_source_lambda_bounds
#print axioms rounded_le_nine_binary
#print axioms binary_half_comparison
#print axioms preliminary_eventual_unclipped
#print axioms rational_entry_eventual_cost
end Paper5.NativeEntry