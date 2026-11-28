import HuberEdgeCorrelation

/-! Different coordinates can receive different normalized positive weights.
One finite maximizer supplies correlations of order each coordinate's own
weight. In particular the two method-specific scales can coexist. -/

namespace WeightedHybrid

open scoped BigOperators
open BangCore (bitSign signedTotal)
open HuberCorrelation (boundedSlope centralIndicator)

variable {E I : Type*} [Fintype E] [Fintype I]

/-- One simultaneous witness from the signed second moment on the *common*
sample space. The inputs can be cut differences on graph edges or centered
cut indicators on vertices. Each unscaled input has energy at least p. -/
theorem weighted_correlation (μ : E → ℚ) (f : I → E → ℚ) (w : I → ℚ) (p : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hw : ∀ i, 0 < w i) (hw1 : ∀ i, w i ≤ 1)
    (hf : ∀ i e, |f i e| ≤ 1) (hp : ∀ i, p ≤ ∑ e, μ e * f i e ^ 2)
    (hmoment : ∀ eps : I → Bool,
      (∑ e, μ e * (signedTotal (fun i e => w i * f i e) eps e) ^ 2) ≤ p) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧
      ∀ i, 3 * p * w i / 16 ≤ |∑ e, μ e * b e * f i e| := by
  let g (i : I) (e : E) := w i * f i e
  have hg (i : I) (e : E) : |g i e| ≤ 1 := by
    change |w i * f i e| ≤ 1
    rw [abs_mul, abs_of_pos (hw i)]
    exact (mul_le_mul (hw1 i) (hf i e) (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  obtain ⟨eps, hmax⟩ :=
    HuberEdgeCorrelation.exists_signs_for_central_energy μ g 1 hμ le_rfl hg
  let z := signedTotal g eps
  let b (e : E) := boundedSlope (z e)
  refine ⟨b, fun e => HuberCorrelation.abs_boundedSlope_le_one _, ?_⟩
  intro i
  let a := w i
  let s := bitSign (eps i)
  let c := ∑ e, μ e * b e * f i e
  let energy := ∑ e, μ e * f i e ^ 2 * centralIndicator (z e)
  have hcentral : 3 * p / 4 ≤ energy :=
    HuberEdgeCorrelation.central_energy_lower_bound μ (f i) z p hμ (hf i) (hp i) (hmoment eps)
  have hdistr : (∑ e, μ e * (g i e)^2 * centralIndicator (z e)) = a^2 * energy := by
    rw [show a^2 * energy = ∑ e, a^2 * (μ e * f i e ^ 2 * centralIndicator (z e)) by
      exact Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun e _ => by dsimp only [g, a]; ring
  have hdistr' : (∑ e, μ e * b e * g i e) = a * c := by
    rw [show a*c = ∑ e, a * (μ e * b e * f i e) by exact Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun e _ => by dsimp only [g, a]; ring
  have hh := hmax i
  simp only [div_one, mul_one] at hh
  change (∑ e, μ e * (g i e)^2 * centralIndicator (z e)) ≤ 4*s*(∑ e, μ e*b e*g i e) at hh
  rw [hdistr, hdistr'] at hh
  have ht := (mul_le_mul_of_nonneg_left hcentral (sq_nonneg a)).trans hh
  have hs : a * (3*p*a/16) ≤ a * (s*c) := by linarith only [ht]
  have hs' := (mul_le_mul_iff_right₀ (hw i)).mp hs
  apply hs'.trans
  change bitSign (eps i) * c ≤ |c|
  cases eps i
  · simpa [bitSign] using neg_le_abs c
  · simpa [bitSign] using le_abs_self c

/-- Combining two estimates uses the common finite sample space. This
two-term bound requires no independence between the two source layouts. -/
theorem combined_moment (μ a b : E → ℚ) (A B : ℚ) (hμ : ∀ e, 0 ≤ μ e)
    (ha : (∑ e, μ e * (a e)^2) ≤ A) (hb : (∑ e, μ e * (b e)^2) ≤ B) :
    (∑ e, μ e * (a e + b e)^2) ≤ 2*(A+B) := by
  calc
    _ ≤ ∑ e, (2*(μ e*(a e)^2) + 2*(μ e*(b e)^2)) := by
      apply Finset.sum_le_sum
      intro e _
      have hx : (a e + b e)^2 ≤ 2*(a e)^2+2*(b e)^2 := by nlinarith [sq_nonneg (a e-b e)]
      calc
        _ ≤ μ e * (2*(a e)^2 + 2*(b e)^2) := mul_le_mul_of_nonneg_left hx (hμ e)
        _ = _ := by ring
    _ = 2 * ((∑ e, μ e*(a e)^2) + ∑ e, μ e*(b e)^2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add ha hb) (by norm_num)

#print axioms weighted_correlation
#print axioms combined_moment

end WeightedHybrid
