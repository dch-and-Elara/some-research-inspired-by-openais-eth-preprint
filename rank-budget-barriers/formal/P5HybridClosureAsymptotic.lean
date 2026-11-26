import P5HybridClosureRates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-! Numerical end of the §8 affine lower bound.  The base-expander
existence and the extraction of logarithmic bounds from the published
parameter formulas are separate from these two asymptotic implications. -/
namespace Paper5.HybridClosure
open scoped BigOperators Topology
open Filter

theorem depth_real_sqrt_lower (γ : ℚ) (hγ : 0<γ) (N k : ℕ) (hk : 0<k) (B : ℝ)
    (hB : 0<B) (hbound : (k:ℝ)≤B) :
    (matchingCoeff γ:ℝ)*(N:ℝ)/(2*Real.sqrt B)<(routeDepth γ N k:ℝ)+1 := by
  have hd : (0:ℝ)<(weightDen k:ℝ) := by
    exact_mod_cast (show 0<weightDen k by unfold weightDen; omega)
  have hc : 0<(matchingCoeff γ:ℝ) := by exact_mod_cast matchingCoeff_pos γ hγ
  have hd₂ : (weightDen k:ℝ)^2≤4*(k:ℝ) := by exact_mod_cast (weightDen_squared k hk).2
  have hs : 0<2*Real.sqrt B := by positivity
  have hu : (weightDen k:ℝ)≤2*Real.sqrt B := by
    apply (sq_le_sq₀ hd.le hs.le).mp
    rw [mul_pow,Real.sq_sqrt hB.le]
    nlinarith only [hd₂,hbound]
  have hf : (matchingCoeff γ:ℝ)*(N:ℝ)*(routeWeight k:ℝ)<(routeDepth γ N k:ℝ)+1 := by
    exact_mod_cast (routeDepth_margin γ hγ N k).2
  calc
    _ ≤ (matchingCoeff γ:ℝ)*(N:ℝ)/(weightDen k:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hd hu
    _ = (matchingCoeff γ:ℝ)*(N:ℝ)*(routeWeight k:ℝ) := by
      simp [routeWeight,div_eq_mul_inv]
    _ < _ := hf

theorem log_scale_gives_eventual_union (Q u : ℕ→ℕ) (C c : ℝ) (hc : 0<c)
    (hlog : ∀ᶠ n : ℕ in atTop,
      (Q n:ℝ)≤C*Real.log (n:ℝ) ∧ (u n:ℝ)≤C*Real.log (n:ℝ)) :
    ∀ᶠ n : ℕ in atTop, 31104*((Q n:ℝ)^2+(u n:ℝ)^2)<c^2*(n:ℝ) := by
  have ht : Tendsto (fun x : ℝ=>Real.log x^2/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have htN : Tendsto (fun n : ℕ=>Real.log (n:ℝ)^2/(n:ℝ)) atTop (𝓝 0) :=
    ht.comp tendsto_natCast_atTop_atTop
  have htc : Tendsto (fun n : ℕ=>62208*C^2*(Real.log (n:ℝ)^2/(n:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using htN.const_mul (62208*C^2)
  have hshort : ∀ᶠ n : ℕ in atTop, 62208*C^2*(Real.log (n:ℝ)^2/(n:ℝ))<c^2 :=
    htc.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<c^2))
  filter_upwards [hlog,hshort,eventually_gt_atTop (0:ℕ)] with n hn hs hpos
  have hpos' : (0:ℝ)<n := by exact_mod_cast hpos
  have hN := (div_lt_iff₀ hpos').mp (by rwa [←mul_div_assoc] at hs)
  have hQ := pow_le_pow_left₀ (show 0≤(Q n:ℝ) by positivity) hn.1 2
  have hu := pow_le_pow_left₀ (show 0≤(u n:ℝ) by positivity) hn.2 2
  nlinarith only [hN,hQ,hu]

theorem logarithmic_routes_depth (γ : ℚ) (hγ : 0<γ) (N Q u : ℕ) (hQ : 0<Q) (hu : 0<u)
    (C : ℝ) (hB : 0<C*Real.log (N:ℝ))
    (hQl : (Q:ℝ)≤C*Real.log (N:ℝ)) (hul : (u:ℝ)≤C*Real.log (N:ℝ)) :
    (matchingCoeff γ:ℝ)*(N:ℝ)/(2*Real.sqrt (C*Real.log (N:ℝ))) <
      ((min (routeDepth γ N Q) (routeDepth γ N u):ℕ):ℝ)+1 := by
  by_cases h : routeDepth γ N Q≤routeDepth γ N u
  · rw [min_eq_left h]
    exact depth_real_sqrt_lower γ hγ N Q hQ _ hB hQl
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    exact depth_real_sqrt_lower γ hγ N u hu _ hB hul

/-- Turn the finite fit into the stated logarithmic depth rate on any
positive logarithmic schedules. Actual placements are still supplied by
the independent layout feasibility lemmas. -/
theorem log_schedules_bigOmega_depth (Q u : ℕ→ℕ) (γ : ℚ) (hγ : 0<γ) (C : ℝ) (hC : 0<C)
    (hlog : ∀ᶠ n : ℕ in atTop, 0<Q n ∧ 0<u n ∧
      (Q n:ℝ)≤C*Real.log (n:ℝ) ∧ (u n:ℝ)≤C*Real.log (n:ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (matchingCoeff γ:ℝ)/(4*Real.sqrt C)*((n:ℝ)/Real.sqrt (Real.log (n:ℝ))) ≤
      ((min (routeDepth γ n (Q n)) (routeDepth γ n (u n)) : ℕ):ℝ) := by
  let c := (matchingCoeff γ:ℝ)
  have hc : 0<c := by dsimp [c]; exact_mod_cast matchingCoeff_pos γ hγ
  have hcast : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLarge : ∀ᶠ n : ℕ in atTop, 16*C/c^2≤(n:ℝ) := hcast.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,hLarge,eventually_gt_atTop (1:ℕ)] with n hn hN h1
  have h1' : (1:ℝ)<n := by exact_mod_cast h1
  have hNpos := zero_lt_one.trans h1'
  have hlogpos : 0<Real.log (n:ℝ) := Real.log_pos h1'
  let B := C*Real.log (n:ℝ)
  have hB : 0<B := mul_pos hC hlogpos
  have hm := logarithmic_routes_depth γ hγ n (Q n) (u n) hn.1 hn.2.1 C hB hn.2.2.1 hn.2.2.2
  have hSqu : (4*Real.sqrt B)^2≤(c*(n:ℝ))^2 := by
    have hN' := (div_le_iff₀ (pow_pos hc 2)).mp hN
    have hL : Real.log (n:ℝ)≤(n:ℝ) := by
      have h := Real.log_le_sub_one_of_pos hNpos
      linarith only [h]
    have h₁ := mul_le_mul_of_nonneg_left hL (show 0≤16*C by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hN' hNpos.le
    rw [mul_pow,mul_pow,Real.sq_sqrt hB.le]
    dsimp [B]
    nlinarith only [h₁,h₂]
  have hD : 2≤c*(n:ℝ)/(2*Real.sqrt B) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.sqrt B)).2
    have h := (sq_le_sq₀ (show 0≤4*Real.sqrt B by positivity)
      (show 0≤c*(n:ℝ) by positivity)).mp hSqu
    linarith only [h]
  change c/(4*Real.sqrt C)*((n:ℝ)/Real.sqrt (Real.log (n:ℝ)))≤_
  have heq : c/(4*Real.sqrt C)*((n:ℝ)/Real.sqrt (Real.log (n:ℝ))) =
      (c*(n:ℝ)/(2*Real.sqrt B))/2 := by
    unfold B
    rw [Real.sqrt_mul hC.le]
    ring
  rw [heq]
  change c*(n:ℝ)/(2*Real.sqrt B)<_ at hm
  linarith only [hm,hD]

#print axioms depth_real_sqrt_lower
#print axioms log_scale_gives_eventual_union
#print axioms logarithmic_routes_depth
#print axioms log_schedules_bigOmega_depth
end Paper5.HybridClosure