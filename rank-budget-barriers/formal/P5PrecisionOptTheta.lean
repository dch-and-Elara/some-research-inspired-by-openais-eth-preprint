import P5PrecisionOptQuantUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Theta

/-! Literal real-valued Θ for the optimum of the fixed retained-jet
decoder. Both constants come from uniform finite inequalities with
arbitrary pointwise legal profiles and independent errors. -/
namespace Paper5.PrecisionOpt
open Filter Asymptotics

theorem quarter_exponent_band (u : ℕ) :
    (2:ℝ)^((7:ℝ)*(u:ℝ)/4) ≤ (2:ℝ)^(2*u-u/4:ℕ) ∧
      (2:ℝ)^(2*u-u/4:ℕ) ≤ 2*(2:ℝ)^((7:ℝ)*(u:ℝ)/4) := by
  let a : ℝ := (7:ℝ)*(u:ℝ)/4
  let e : ℕ := 2*u-u/4
  have hm := Nat.div_add_mod u 4
  have hb := Nat.mod_lt u (by decide : 0<4)
  have hL : 4*(u/4)≤u := by omega
  have hU : u≤4*(u/4)+3 := by omega
  have h1 : (4:ℝ)*((u/4:ℕ):ℝ)≤(u:ℝ) := by exact_mod_cast hL
  have h2 : (u:ℝ)≤(4:ℝ)*((u/4:ℕ):ℝ)+3 := by exact_mod_cast hU
  have he0 : u/4≤2*u := by omega
  have he : (e:ℝ)=2*(u:ℝ)-((u/4:ℕ):ℝ) := by
    dsimp [e]
    rw [Nat.cast_sub he0]
    push_cast
    rfl
  have heta : a≤(e:ℝ) := by dsimp [a]; rw [he]; linarith
  have hte : (e:ℝ)≤a+1 := by dsimp [a]; rw [he]; linarith
  change (2:ℝ)^a ≤ (2:ℝ)^e ∧ (2:ℝ)^e≤2*(2:ℝ)^a
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) heta).trans_eq (Real.rpow_natCast _ _)
  · rw [←Real.rpow_natCast]
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hte).trans_eq ?_
    rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]

noncomputable def optimizedScale (M u : ℕ) : ℝ :=
  (M:ℝ)*(2:ℝ)^((7:ℝ)*(u:ℝ)/4)/((u:ℝ)*(u:ℝ))

theorem optimizedScale_nonnegative (M u : ℕ) : 0≤optimizedScale M u := by
  unfold optimizedScale
  positivity

theorem optimized_root_real_bounds {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 16≤u) (hM : u*u≤M) (p : ℕ) :
    optimizedScale M u / 2 ≤ (exactRootOpt M u p:ℝ) ∧
      (exactRootOpt M u p:ℝ) ≤ 600*optimizedScale M u := by
  obtain ⟨hL,hU⟩ := optimized_root_two_sided O hn2 hu hM p
  obtain ⟨ha,hb⟩ := quarter_exponent_band u
  let x : ℝ := u
  let m : ℝ := M
  let b : ℝ := exactRootOpt M u p
  let T : ℝ := (2:ℝ)^(2*u-u/4:ℕ)
  let S : ℝ := (2:ℝ)^((7:ℝ)*(u:ℝ)/4)
  have hx : 0<x := by dsimp [x]; exact_mod_cast (show 0<u by omega)
  have hxx : 0<x*x := mul_pos hx hx
  have hm : 0≤m := by dsimp [m]; positivity
  have hL' : m*T≤2*(x*x)*b := by dsimp [m,T,x,b]; exact_mod_cast hL
  have hU' : (x*x)*b≤300*m*T := by dsimp [m,T,x,b]; exact_mod_cast hU
  have hLS : m*S≤2*(x*x)*b := (mul_le_mul_of_nonneg_left ha hm).trans hL'
  have hUS : (x*x)*b≤600*(m*S) := by
    calc
      _ ≤ 300*m*T := hU'
      _ ≤ (300*m)*(2*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  change (m*S/(x*x))/2≤b ∧ b≤600*(m*S/(x*x))
  constructor
  · rw [div_div]
    apply (div_le_iff₀ (mul_pos hxx (by norm_num : 0<(2:ℝ)))).mpr
    calc
      m*S≤2*(x*x)*b := hLS
      _ = b*(x*x*2) := by ring
  · calc
      b ≤ (600*(m*S))/(x*x) := by
        apply (le_div_iff₀ hxx).mpr
        calc
          b*(x*x) = (x*x)*b := mul_comm ..
          _ ≤ _ := hUS
      _ = 600*(m*S/(x*x)) := mul_div_assoc ..

theorem optimized_root_isTheta_of_eventual_guards {K : Type*} [Field K] [CharZero K]
    (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) (M u p : ℕ→ℕ)
    (h : ∀ᶠ n in atTop,16≤u n ∧ u n*u n≤M n) :
    (fun n => (exactRootOpt (M n) (u n) (p n):ℝ)) =Θ[atTop]
      (fun n => optimizedScale (M n) (u n)) := by
  constructor
  · apply IsBigO.of_bound 600
    filter_upwards [h] with n hn
    have H := (optimized_root_real_bounds O hn2 hn.1 hn.2 (p n)).2
    simpa only [Real.norm_of_nonneg (optimizedScale_nonnegative _ _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)] using H
  · apply IsBigO.of_bound 2
    filter_upwards [h] with n hn
    have H := (optimized_root_real_bounds O hn2 hn.1 hn.2 (p n)).1
    have hN : optimizedScale (M n) (u n) ≤ 2*(exactRootOpt (M n) (u n) (p n):ℝ) := by linarith
    simpa only [Real.norm_of_nonneg (optimizedScale_nonnegative _ _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)] using hN

theorem optimized_root_isTheta_source_regime {K : Type*} [Field K] [CharZero K]
    (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) (M u p : ℕ→ℕ)
    (hu : Tendsto u atTop atTop)
    (hM : Tendsto (fun n => (M n:ℝ)/((u n:ℝ)*(u n:ℝ))) atTop atTop) :
    (fun n => (exactRootOpt (M n) (u n) (p n):ℝ)) =Θ[atTop]
      (fun n => optimizedScale (M n) (u n)) := by
  apply optimized_root_isTheta_of_eventual_guards O hn2 M u p
  have H1 := tendsto_atTop.1 hu 16
  have H2 := tendsto_atTop.1 hM 1
  filter_upwards [H1,H2] with n hn he
  refine ⟨hn,?_⟩
  have hp : 0<(u n:ℝ) := by exact_mod_cast (show 0<u n by omega)
  have HR := (le_div_iff₀ (mul_pos hp hp)).mp he
  rw [one_mul] at HR
  exact_mod_cast HR

#print axioms quarter_exponent_band
#print axioms optimized_root_real_bounds
#print axioms optimized_root_isTheta_of_eventual_guards
#print axioms optimized_root_isTheta_source_regime
end Paper5.PrecisionOpt
