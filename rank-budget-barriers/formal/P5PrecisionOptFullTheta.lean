import P5PrecisionOptAllNativeScale

/-! Real-valued Θ for the unoptimized profile stated before (P.4).
This is a comparison for the same fixed retained-jet Hermite decoder. -/
namespace Paper5.PrecisionOpt
open Filter Asymptotics

noncomputable def allNativeScale (M u : ℕ) : ℝ :=
  (M:ℝ)*(2:ℝ)^u/((u:ℝ)*(u:ℝ))

theorem all_native_real_bounds {K : Type*} [Field K] [CharZero K] (O : Subring K)
    [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) {M u : ℕ} (hu : 4≤u) (hM : u≤M) (p : ℕ) :
    allNativeScale M u ≤ (profileCap M u p (allNativeProfile M u):ℝ) ∧
      (profileCap M u p (allNativeProfile M u):ℝ) ≤ 100*allNativeScale M u := by
  obtain ⟨hL,hU⟩ := all_native_profile_two_sided O hn2 hu hM p
  let x : ℝ := u
  let N : ℝ := (M:ℝ)*(2:ℝ)^u
  let b : ℝ := profileCap M u p (allNativeProfile M u)
  have hx : 0<x := by dsimp [x]; exact_mod_cast (show 0<u by omega)
  have hxx : 0<x*x := mul_pos hx hx
  have h1 : N≤(x*x)*b := by dsimp [N,x,b]; exact_mod_cast hL
  have h2 : (x*x)*b≤100*N := by dsimp [N,x,b]; exact_mod_cast hU
  change N/(x*x)≤b ∧ b≤100*(N/(x*x))
  constructor
  · apply (div_le_iff₀ hxx).mpr
    exact h1.trans_eq (mul_comm ..)
  · calc
      b≤100*N/(x*x) := (le_div_iff₀ hxx).mpr ((mul_comm ..).trans_le h2)
      _ = _ := mul_div_assoc ..

theorem all_native_isTheta_source_regime {K : Type*} [Field K] [CharZero K]
    (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O)) (M u p : ℕ→ℕ)
    (hu : Tendsto u atTop atTop)
    (hM : Tendsto (fun n => (M n:ℝ)/((u n:ℝ)*(u n:ℝ))) atTop atTop) :
    (fun n => (profileCap (M n) (u n) (p n) (allNativeProfile (M n) (u n)):ℝ)) =Θ[atTop]
      (fun n => allNativeScale (M n) (u n)) := by
  have h : ∀ᶠ n in atTop,4≤u n ∧ u n≤M n := by
    filter_upwards [tendsto_atTop.1 hu 4,tendsto_atTop.1 hM 1] with n hn hm
    have hp : 0<(u n:ℝ) := by exact_mod_cast (show 0<u n by omega)
    have HR := (le_div_iff₀ (mul_pos hp hp)).mp hm
    rw [one_mul] at HR
    have hM' : u n*u n≤M n := by exact_mod_cast HR
    exact ⟨hn,(show u n≤u n*u n by nlinarith).trans hM'⟩
  have hScale (n : ℕ) : 0≤allNativeScale (M n) (u n) := by unfold allNativeScale; positivity
  constructor
  · apply IsBigO.of_bound 100
    filter_upwards [h] with n hn
    have H := (all_native_real_bounds O hn2 hn.1 hn.2 (p n)).2
    simpa only [Real.norm_of_nonneg (hScale n),Real.norm_of_nonneg (Nat.cast_nonneg _)] using H
  · apply IsBigO.of_bound' 
    filter_upwards [h] with n hn
    have H := (all_native_real_bounds O hn2 hn.1 hn.2 (p n)).1
    simpa only [Real.norm_of_nonneg (hScale n),Real.norm_of_nonneg (Nat.cast_nonneg _)] using H

#print axioms all_native_real_bounds
#print axioms all_native_isTheta_source_regime
end Paper5.PrecisionOpt
