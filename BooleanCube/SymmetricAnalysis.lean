import BooleanCube.Binomial
import BooleanCube.RealBudget
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LocalReconstruction
open Filter
open scoped Topology
noncomputable section

private theorem nat_atTop_real : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

theorem symmetric_log_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp nat_atTop_real

theorem symmetric_cut_threshold (γ t : ℝ) (hγ : 1/2 < γ) :
    ∃ l : ℕ → ℕ, (∀ᶠ q : ℕ in atTop, 2*l q < q) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ᶠ q : ℕ in atTop,
        (q:ℝ)-2*l q ≤ M*Real.sqrt ((q:ℝ)*Real.log q)) ∧
      Tendsto (fun q : ℕ => ((q:ℝ)-2*l q)/q) atTop (𝓝 0) ∧
      Tendsto (fun q : ℕ => (q:ℝ)/((q:ℝ)-2*l q)^2) atTop (𝓝 0) ∧
      Tendsto (fun q : ℕ => ((q:ℝ)-2*l q)^2/q-(2*γ-1)*Real.log q) atTop
        (𝓝 (Real.log (8/Real.pi)+t)) := by
  let c := 2*γ-1
  let B := Real.log (8/Real.pi)+t
  let f (q : ℕ) := c*Real.log q+B
  let x (q : ℕ) := Real.sqrt ((q:ℝ)*f q)
  let l (q : ℕ) := ⌊((q:ℝ)-x q)/2⌋₊
  let g (q : ℕ) := (q:ℝ)-2*l q
  have hc : 0 < c := by dsimp [c]; linarith
  have hf : Tendsto f atTop atTop :=
    tendsto_atTop_add_const_right _ B (symmetric_log_atTop.const_mul_atTop hc)
  have qp := nat_atTop_real.eventually_gt_atTop 0
  have invq : Tendsto (fun q : ℕ => 1/(q:ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have fdiv : Tendsto (fun q : ℕ => f q/q) atTop (𝓝 0) := by
    have logdiv := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp nat_atTop_real
    have h := (logdiv.const_mul c).add (invq.const_mul B)
    simpa only [Function.comp_def, f, add_div, mul_div_assoc, add_zero, mul_zero,
      mul_one_div] using h
  have xdiv : Tendsto (fun q : ℕ => x q/q) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp fdiv
    rw [Real.sqrt_zero] at hs
    apply hs.congr'
    filter_upwards [qp] with q hq
    change Real.sqrt (f q/q) = x q/q
    apply (eq_div_iff hq.ne').mpr
    calc
      _ = Real.sqrt ((q:ℝ)^2*(f q/q)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq.le, mul_comm]
      _ = x q := by
        dsimp only [x]
        congr 1
        field_simp
  have bounds : ∀ᶠ q : ℕ in atTop,
      0 < x q ∧ x q ≤ g q ∧ g q < x q+2 ∧ x q ^ 2 = (q:ℝ)*f q := by
    filter_upwards [hf.eventually_gt_atTop 0, qp, xdiv.eventually (gt_mem_nhds zero_lt_one)] with q hp hq hsmall
    change x q/q < 1 at hsmall
    have hn : 0 ≤ ((q:ℝ)-x q)/2 := by linarith [(div_lt_iff₀ hq).mp hsmall]
    have hlo := Nat.floor_le hn
    have hhi := Nat.lt_floor_add_one (((q:ℝ)-x q)/2)
    exact ⟨Real.sqrt_pos.mpr (mul_pos hq hp), by dsimp only [g,l]; linarith,
      by dsimp only [g,l]; linarith, Real.sq_sqrt (mul_nonneg hq.le hp.le)⟩
  have small : Tendsto (fun q : ℕ => g q/q) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (g := fun q => x q/q + 2*(1/(q:ℝ))) (by simpa using xdiv.add (invq.const_mul 2))
    · filter_upwards [bounds, qp] with q hb hq
      exact div_nonneg (hb.1.le.trans hb.2.1) hq.le
    · filter_upwards [bounds, qp] with q hb hq
      rw [mul_one_div, ← add_div]
      exact div_le_div_of_nonneg_right hb.2.2.1.le hq.le
  refine ⟨l, ?_, ?_, small, ?_, ?_⟩
  · filter_upwards [bounds] with q hb
    have : 2*(l q:ℝ) < q := by dsimp only [g] at hb; linarith [hb.1, hb.2.1]
    exact_mod_cast this
  · let A := c+|B|+1
    have hA : 0 < A := by dsimp [A]; linarith [abs_nonneg B]
    refine ⟨Real.sqrt A+2, by positivity, ?_⟩
    have hprod := nat_atTop_real.atTop_mul_atTop₀ symmetric_log_atTop
    filter_upwards [bounds, qp, symmetric_log_atTop.eventually_ge_atTop 1,
      (Real.tendsto_sqrt_atTop.comp hprod).eventually_ge_atTop 1] with q hb hq hl hroot
    change 1 ≤ Real.log q at hl
    change 1 ≤ Real.sqrt ((q:ℝ)*Real.log q) at hroot
    have hs : f q ≤ A*Real.log q := by
      dsimp only [A,f]
      nlinarith only [le_abs_self B, mul_nonneg (abs_nonneg B) (sub_nonneg.mpr hl), hl]
    have hu : x q ≤ Real.sqrt A * Real.sqrt ((q:ℝ)*Real.log q) := by
      rw [← Real.sqrt_mul hA.le]
      apply Real.sqrt_le_sqrt
      dsimp only [x]
      nlinarith only [mul_le_mul_of_nonneg_left hs hq.le]
    change g q ≤ _
    linarith [hb.2.2.1]
  · refine squeeze_zero' (g := fun q => 1/f q) (Eventually.of_forall fun q =>
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ?_ (by
        simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hf)
    filter_upwards [bounds, qp, hf.eventually_gt_atTop 0] with q hb hq hp
    have hsq := (sq_le_sq₀ hb.1.le (hb.1.le.trans hb.2.1)).mpr hb.2.1
    apply (div_le_div_iff₀ (sq_pos_of_pos (hb.1.trans_le hb.2.1)) hp).mpr
    simpa only [one_mul, ← hb.2.2.2] using hsq
  · have err : Tendsto (fun q : ℕ => g q^2/q-f q) atTop (𝓝 0) := by
      refine squeeze_zero' (g := fun q => 4*(x q/q+1/(q:ℝ))) ?_ ?_
        (by simpa using (xdiv.add invq).const_mul 4)
      · filter_upwards [bounds, qp] with q hb hq
        have hsq := (sq_le_sq₀ hb.1.le (hb.1.le.trans hb.2.1)).mpr hb.2.1
        apply sub_nonneg.mpr
        apply (le_div_iff₀ hq).mpr
        linarith only [hsq, hb.2.2.2]
      · filter_upwards [bounds, qp] with q hb hq
        have hs := (sq_le_sq₀ (hb.1.le.trans hb.2.1) (by linarith [hb.1])).mpr hb.2.2.1.le
        have he : f q = x q^2/q := (eq_div_iff hq.ne').mpr (by linarith only [hb.2.2.2])
        rw [he, ← sub_div, ← add_div, ← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hq.le
        nlinarith only [hs, hb.2.2.2]
    change Tendsto (fun q => g q^2/q-c*Real.log q) atTop (𝓝 B)
    apply (show Tendsto (fun q => (g q^2/q-f q)+B) atTop (𝓝 B) by simpa using err.add_const B).congr
    intro q
    unfold f
    ring

/-- Uniform logarithmic cost of a deleted layer in units of the original budget. -/
theorem symmetric_local_log_cost (γ M η : ℝ) (hM : 0 < M) (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ k : ℕ, k ≤ q →
      |(q:ℝ)-2*k| ≤ M*Real.sqrt ((q:ℝ)*Real.log q) →
      |Real.log ((q.choose k:ℝ)/measurementBudget q γ) -
        (Real.log (8/Real.pi)/2-Real.log 2 +
          ((2*γ-1)*Real.log q - ((q:ℝ)-2*k)^2/q)/2)| ≤ η := by
  have sqdiv := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero.comp
    nat_atTop_real
  let C := 3+4*M^2+48*M^4
  have err : Tendsto (fun q : ℕ => C*(Real.log q)^2/q) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one, Real.rpow_two, mul_div_assoc, mul_zero]
      using sqdiv.const_mul C
  filter_upwards [uniform_local_binomial M hM, err.eventually (gt_mem_nhds hη),
    nat_atTop_real.eventually_gt_atTop 0] with q hloc herr hq
  intro k hk hw
  have hw' : |(k:ℝ)-q/2| ≤ M*Real.sqrt ((q:ℝ)*Real.log q) := by
    rw [show (k:ℝ)-q/2 = -( ((q:ℝ)-2*k)/2) by ring, abs_neg, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg ((q:ℝ)-2*k)]
  have choose_pos : 0 < (q.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hk
  have hpow : 0 < (2:ℝ)^q := by positivity
  have hp : 0 < (q:ℝ)^γ := Real.rpow_pos_of_pos hq _
  have hl : Real.log ((q.choose k:ℝ)/measurementBudget q γ) =
      Real.log ((q.choose k:ℝ)/(2:ℝ)^q)+γ*Real.log q := by
    rw [measurementBudget, Real.log_div choose_pos.ne' (div_pos hpow hp).ne',
      Real.log_div hpow.ne' hp.ne', Real.log_div choose_pos.ne' hpow.ne', Real.log_rpow hq]
    ring
  have hconst : Real.log (8/Real.pi)/2-Real.log 2 = Real.log (2/Real.pi)/2 := by
    rw [Real.log_div (by norm_num) Real.pi_pos.ne', Real.log_div (by norm_num) Real.pi_pos.ne',
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    ring
  have hquad : ((q:ℝ)-2*k)^2/q/2 = 2*((k:ℝ)-q/2)^2/q := by ring
  have eq : Real.log ((q.choose k:ℝ)/measurementBudget q γ) -
      (Real.log (8/Real.pi)/2-Real.log 2 +
        ((2*γ-1)*Real.log q - ((q:ℝ)-2*k)^2/q)/2) =
      Real.log ((q.choose k:ℝ)/(2:ℝ)^q) -
        ((Real.log (2/Real.pi)-Real.log q)/2 - 2*((k:ℝ)-q/2)^2/q) := by
    rw [hl, hconst, sub_div, hquad]
    ring
  rw [eq]
  exact (hloc k hw').trans herr.le

private theorem gaussian_deriv {Q : ℝ} (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y^2/(2*Q)))
      (Real.exp (-x^2/(2*Q)) * (-x/Q)) x := by
  convert (((hasDerivAt_pow 2 x).neg.div_const (2*Q)).exp) using 1
  simp only [Pi.neg_apply, Nat.cast_ofNat]
  by_cases h : Q = 0
  · simp [h]
  · field_simp
    ring

/-- The Gaussian midpoint bound holds outside its central concave interval. -/
theorem symmetric_gaussian_midpoint {Q a b : ℝ} (hQ : 0 < Q)
    (ha : Real.sqrt Q ≤ a) (hb : Real.sqrt Q ≤ b) :
    2*Real.exp (-(a+b)^2/(8*Q)) ≤ Real.exp (-a^2/(2*Q))+Real.exp (-b^2/(2*Q)) := by
  let G := fun y : ℝ => Real.exp (-y^2/(2*Q))
  let G' := fun y : ℝ => G y * (-y/Q)
  have hG (x : ℝ) : HasDerivAt G (G' x) x := gaussian_deriv x
  have hG' (x : ℝ) : HasDerivAt G' (G x * ((x^2-Q)/Q^2)) x := by
    convert (hG x).mul ((hasDerivAt_id x).neg.div_const Q) using 1
    simp only [G', Pi.neg_apply, id_eq]
    field_simp
    ring
  have convex : ConvexOn ℝ (Set.Ici (Real.sqrt Q)) G := by
    apply convexOn_of_deriv2_nonneg (convex_Ici _) (fun x _ => (hG x).continuousAt.continuousWithinAt)
      (fun x _ => (hG x).differentiableAt.differentiableWithinAt)
    · intro x _
      have eq : deriv G = G' := funext fun y => (hG y).deriv
      rw [eq]
      exact (hG' x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : Real.sqrt Q ≤ x := interior_subset hx
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg Q) ((Real.sqrt_nonneg Q).trans hx')).mpr hx'
      rw [Real.sq_sqrt hQ.le] at hsq
      have eq : deriv G = G' := funext fun y => (hG y).deriv
      rw [Function.iterate_succ_apply', Function.iterate_one, eq, (hG' x).deriv]
      exact mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_nonneg.mpr hsq) (sq_nonneg _))
  have h := convex.2 (x := a) (y := b) ha hb
    (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)
  simp only [smul_eq_mul, G] at h
  rw [show -((1/2:ℝ)*a+1/2*b)^2/(2*Q) = -(a+b)^2/(8*Q) by ring] at h
  linarith only [h]

end
end LocalReconstruction
