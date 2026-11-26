import S6Published

namespace Section6

open Filter
open scoped Topology

noncomputable section

lemma eventually_poly_le_exp (d : ℕ) (c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, c*(m : ℝ)^d ≤ Real.exp (a*(m : ℝ)) := by
  have hSmall := (Real.isLittleO_pow_exp_atTop (n := d)).bound (div_pos (pow_pos ha d) hc)
  have ht : Tendsto (fun m : ℕ => a*(m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  filter_upwards [ht.eventually hSmall] with m hm
  have hp : 0 ≤ (a*(m : ℝ))^d := by positivity
  change ‖(a*(m : ℝ))^d‖ ≤ a^d/c * ‖Real.exp (a*(m : ℝ))‖ at hm
  rw [Real.norm_of_nonneg hp, Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow] at hm
  have h := mul_le_mul_of_nonneg_left hm hc.le
  have h₁ : c*(a^d/c*Real.exp (a*(m : ℝ))) = a^d*Real.exp (a*(m : ℝ)) := by
    field_simp
  rw [h₁] at h
  apply (mul_le_mul_iff_right₀ (pow_pos ha d)).mp
  linarith only [h]

lemma lambda_exp_le_n {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (Real.log 2 * ((publishedLambda n : ℝ)-1)) ≤ n := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlg : 0 ≤ lg (n : ℝ) := div_nonneg hlog logTwo_pos.le
  have hround := Nat.ceil_lt_add_one hlg
  change (publishedLambda n : ℝ) < lg (n : ℝ) + 1 at hround
  have hh : (publishedLambda n : ℝ) - 1 ≤ lg (n : ℝ) := by linarith only [hround]
  have ht := (le_div_iff₀ logTwo_pos).mp hh
  have hy : Real.log 2 * ((publishedLambda n : ℝ)-1) ≤ Real.log (n : ℝ) := by
    linarith only [ht]
  have he := Real.exp_le_exp.mpr hy
  rw [Real.exp_log (by exact_mod_cast (show 0 < n by omega))] at he
  exact he

lemma eventually_room (B : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      4*(publishedLambda n : ℝ)^B * Real.exp (Real.log 2 * (publishedLambda n : ℝ)/64) ≤ n ∧
      2*(publishedLambda n : ℝ)^2 ≤ n := by
  have ha : 0 < Real.log 2 * (63/64) := by linarith only [logTwo_pos]
  filter_upwards [lambda_atTop.eventually (eventually_poly_le_exp B 8 _ (by norm_num) ha),
    lambda_atTop.eventually (eventually_poly_le_exp 2 4 _ (by norm_num) logTwo_pos),
    eventually_ge_atTop (1 : ℕ)] with n h₁ h₂ hn
  let lam := (publishedLambda n : ℝ)
  have hcap := lambda_exp_le_n hn
  have he : Real.exp (Real.log 2 * lam) =
      2 * Real.exp (Real.log 2 * (lam-1)) := by
    have h : Real.log 2 * lam = Real.log 2 + Real.log 2 * (lam-1) := by ring
    rw [h, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hex := mul_le_mul_of_nonneg_right h₁ (Real.exp_nonneg (Real.log 2 * lam/64))
  rw [← Real.exp_add] at hex
  have hh : Real.log 2 * (63/64) * lam + Real.log 2 * lam/64 = Real.log 2 * lam := by ring
  rw [hh,he] at hex
  rw [he] at h₂
  constructor <;> linarith only [hcap,hex,h₂]

lemma dimension_sq_le_exp {Q r lam : ℕ} (hr : 0 < r)
    (hD : lg (paperD Q r) ≤ (lam : ℝ)/128) :
    (paperD Q r : ℝ)^2 ≤ Real.exp (Real.log 2*(lam : ℝ)/64) := by
  have hd : (0 : ℝ) < paperD Q r := by
    exact_mod_cast (Nat.pow_pos hr : 0 < r^(2*Q))
  have h := (div_le_iff₀ logTwo_pos).mp hD
  have he : Real.log ((paperD Q r : ℝ)^2) ≤ Real.log 2*(lam : ℝ)/64 := by
    rw [Real.log_pow]
    norm_num
    linarith only [h]
  have hh := Real.exp_le_exp.mpr he
  rwa [Real.exp_log (by positivity)] at hh

/-- The source hypothesis b,w ≤ λ^B and n ≤ M implies both balance checks
simultaneously, uniformly in the actual incidence system at each size. -/
theorem eventually_numeric_layout (B : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let lam := publishedLambda n
      let nu := publishedNu lam
      let r := publishedRGroups lam nu
      let Q := publishedQ lam nu
      Rounded B lam ∧
      ∀ b w M : ℕ, b ≤ lam^B → w ≤ lam^B → n ≤ M →
        2*(b+w)*(paperD Q r)^2 ≤ M ∧ 2*Q*r^2 ≤ n := by
  filter_upwards [lambda_atTop.eventually (eventually_rounded B), eventually_room B] with n hp hroom
  refine ⟨hp, ?_⟩
  intro b w M hb hw hM
  let lam := publishedLambda n
  let nu := publishedNu lam
  let r := publishedRGroups lam nu
  let Q := publishedQ lam nu
  have hr : 0 < r := by have hh : 2 ≤ r := hp.groups; omega
  have hd := dimension_sq_le_exp hr hp.dimLog
  have hn : (n : ℝ) ≤ M := by exact_mod_cast hM
  have hc : 2*((b : ℝ)+w) ≤ 4*(lam : ℝ)^B := by
    have h₁ : (b : ℝ) ≤ (lam : ℝ)^B := by exact_mod_cast hb
    have h₂ : (w : ℝ) ≤ (lam : ℝ)^B := by exact_mod_cast hw
    linarith only [h₁,h₂]
  have hu : 2*((b : ℝ)+w)*(paperD Q r : ℝ)^2 ≤ M :=
    (mul_le_mul hc hd (sq_nonneg _) (by positivity)).trans (hroom.1.trans hn)
  have hν : (1 : ℝ) ≤ 128*(nu : ℝ) := by
    have h : (1 : ℝ) ≤ nu := by exact_mod_cast hp.hNu
    linarith only [h]
  have hQhi : (Q : ℝ)*128*nu ≤ lam := by exact_mod_cast hp.qMul
  have hQ : (Q : ℝ) ≤ lam := by
    have h := mul_le_mul_of_nonneg_left hν (show (0 : ℝ) ≤ Q by positivity)
    linarith only [h,hQhi]
  have hr₂ : (r : ℝ)^2 ≤ lam := by exact_mod_cast hp.rSq
  have hh := mul_le_mul hQ hr₂ (sq_nonneg _) (show (0 : ℝ) ≤ lam by positivity)
  have hgrp : 2*(Q : ℝ)*(r : ℝ)^2 ≤ n := by
    nlinarith only [hh,hroom.2]
  exact ⟨by exact_mod_cast hu, by exact_mod_cast hgrp⟩

#print axioms eventually_room
#print axioms eventually_numeric_layout

end
end Section6


