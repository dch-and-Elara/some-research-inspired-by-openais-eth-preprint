import HuberPotential
import BangCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

/-! A finite rational simultaneous-correlation lemma. Maximization over the
whole sign cube produces one bounded witness for all the functions. -/

namespace HuberCorrelation

open scoped BigOperators
open BangCore (bitSign signedTotal)
open HuberPotential (rho slope)

variable {E I : Type*} [Fintype E] [Fintype I]

private theorem sum_div_constant (g : E → ℚ) (c : ℚ) :
    (∑ e, g e) / c = ∑ e, g e / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Indicator of the interval on which a flip of size at most two has a full
quadratic remainder. -/
def centralIndicator (x : ℚ) : ℚ := if -2 ≤ x ∧ x ≤ 2 then 1 else 0

/-- A finite second-moment bound puts at least three quarters of the mass
in the central interval. -/
theorem central_mass (μ w : E → ℚ) (hμ : ∀ e, 0 ≤ μ e)
    (hmass : ∑ e, μ e = 1) (hmoment : ∑ e, μ e * w e ^ 2 ≤ 1) :
    (3 / 4 : ℚ) ≤ ∑ e, μ e * centralIndicator (w e) := by
  have hpoint (x : ℚ) : 4 - x ^ 2 ≤ 4 * centralIndicator x := by
    by_cases hl : -2 ≤ x
    · by_cases hu : x ≤ 2
      · simp only [centralIndicator, hl, hu, and_self, if_true, mul_one]
        linarith only [sq_nonneg x]
      · simp only [centralIndicator, hu, and_false, if_false, mul_zero]
        nlinarith [sq_nonneg (x - 2)]
    · simp only [centralIndicator, hl, false_and, if_false, mul_zero]
      nlinarith [sq_nonneg (x + 2)]
  have hsum : 4 * (∑ e, μ e) - (∑ e, μ e * w e ^ 2) ≤
      4 * ∑ e, μ e * centralIndicator (w e) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    calc
      4 * μ e - μ e * w e ^ 2 = μ e * (4 - w e ^ 2) := by ring
      _ ≤ μ e * (4 * centralIndicator (w e)) :=
        mul_le_mul_of_nonneg_left (hpoint (w e)) (hμ e)
      _ = _ := by ring
  rw [hmass] at hsum
  linarith only [hsum, hmoment]

/-- One quarter of the Huber slope lies in the unit interval in absolute value. -/
def boundedSlope (x : ℚ) : ℚ := slope x / 4

theorem abs_boundedSlope_le_one (x : ℚ) : |boundedSlope x| ≤ 1 := by
  obtain ⟨hl, hu⟩ := HuberPotential.slope_bound x
  rw [boundedSlope, abs_le]
  constructor <;> linarith

/-- Pointwise gain for one sign flip, keeping a uniform lower bound on the
quadratic gain inside the central interval. -/
theorem flip_lower_bound (x v δ : ℚ) (s : Bool) (hδ : 0 ≤ δ)
    (hl : δ ≤ |v|) (hu : |v| ≤ 1) :
    -8 * bitSign s * (boundedSlope x * v) + 2 * δ ^ 2 * centralIndicator x ≤
      rho (x - 2 * bitSign s * v) - rho x := by
  have hv := abs_le.mp hu
  have hstep : -2 ≤ 2 * bitSign s * v ∧ 2 * bitSign s * v ≤ 2 := by
    cases s <;> constructor <;> norm_num [bitSign] <;> linarith [hv.1, hv.2]
  have hsquare : δ ^ 2 ≤ v ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hδ (abs_nonneg v)).mpr hl
  have hgain : 2 * δ ^ 2 * centralIndicator x ≤
      (if -2 ≤ x ∧ x ≤ 2 then (2 * bitSign s * v) ^ 2 / 2 else 0) := by
    by_cases hx : -2 ≤ x ∧ x ≤ 2
    · simp only [centralIndicator, if_pos hx, mul_pow, BangCore.bitSign_sq, mul_one]
      linarith only [hsquare]
    · simp [centralIndicator, hx]
  calc
    _ = -(2 * bitSign s * v) * slope x + 2 * δ ^ 2 * centralIndicator x := by
      unfold boundedSlope
      ring
    _ ≤ _ := add_le_add_left hgain _
    _ ≤ _ := HuberPotential.flip_remainder x (2 * bitSign s * v) hstep.1 hstep.2

/-- The maximizing signs certify all signed correlations for normalized input
functions with uniformly bounded signed second moment. -/
theorem exists_normalized_signed_correlations (μ : E → ℚ) (v : I → E → ℚ) (δ : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hmass : ∑ e, μ e = 1) (hδ : 0 ≤ δ)
    (hl : ∀ i e, δ ≤ |v i e|) (hu : ∀ i e, |v i e| ≤ 1)
    (hmoment : ∀ eps : I → Bool, (∑ e, μ e * (signedTotal v eps e) ^ 2) ≤ 1) :
    ∃ (eps : I → Bool) (b : E → ℚ), (∀ e, |b e| ≤ 1) ∧
      ∀ i, 3 * δ ^ 2 / 16 ≤ bitSign (eps i) * ∑ e, μ e * b e * v i e := by
  classical
  let objective (eps : I → Bool) := ∑ e, μ e * rho (signedTotal v eps e)
  obtain ⟨eps, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (I → Bool)) objective Finset.univ_nonempty
  let w := signedTotal v eps
  refine ⟨eps, fun e => boundedSlope (w e), fun e => abs_boundedSlope_le_one _, ?_⟩
  have hcentral := central_mass μ w hμ hmass (hmoment eps)
  intro i
  let r := bitSign (eps i)
  have hflip : (∑ e, μ e * rho (w e - 2 * r * v i e)) ≤
      ∑ e, μ e * rho (w e) := by
    have h := hmax (Function.update eps i (!(eps i))) (Finset.mem_univ _)
    dsimp only [objective] at h
    rw [BangCore.flip_identity] at h
    exact h
  have hsum :
      -8 * r * (∑ e, μ e * boundedSlope (w e) * v i e) +
          2 * δ ^ 2 * (∑ e, μ e * centralIndicator (w e)) ≤
        (∑ e, μ e * rho (w e - 2 * r * v i e)) - ∑ e, μ e * rho (w e) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have h := mul_le_mul_of_nonneg_left
      (flip_lower_bound (w e) (v i e) δ (eps i) hδ (hl i e) (hu i e)) (hμ e)
    dsimp only [r]
    linarith only [h]
  have hc := mul_le_mul_of_nonneg_left hcentral (show 0 ≤ 2 * δ ^ 2 by positivity)
  change 3 * δ ^ 2 / 16 ≤ r * ∑ e, μ e * boundedSlope (w e) * v i e
  linarith only [hsum, hflip, hc]

/-- One bounded rational function has the stated absolute correlation with
every input function. The moment hypothesis concerns the unscaled signed sums. -/
theorem exists_simultaneous_correlation (μ : E → ℚ) (f : I → E → ℚ) (η H : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hmass : ∑ e, μ e = 1) (hη : 0 ≤ η) (hH : 1 ≤ H)
    (hl : ∀ i e, η ≤ |f i e|) (hu : ∀ i e, |f i e| ≤ 1)
    (hmoment : ∀ eps : I → Bool, (∑ e, μ e * (signedTotal f eps e) ^ 2) ≤ H ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧
      ∀ i, 3 * η ^ 2 / (16 * H) ≤ |∑ e, μ e * b e * f i e| := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let v (i : I) (e : E) := f i e / H
  have hvl (i : I) (e : E) : η / H ≤ |v i e| := by
    change η / H ≤ |f i e / H|
    rw [abs_div, abs_of_pos hHpos, div_le_div_iff_of_pos_right hHpos]
    exact hl i e
  have hvu (i : I) (e : E) : |v i e| ≤ 1 := by
    change |f i e / H| ≤ 1
    rw [abs_div, abs_of_pos hHpos, div_le_one hHpos]
    exact (hu i e).trans hH
  have htotal (eps : I → Bool) (e : E) :
      signedTotal v eps e = signedTotal f eps e / H := by
    simp only [signedTotal, v, ← mul_div_assoc, sum_div_constant]
  have hnormalized (eps : I → Bool) : (∑ e, μ e * (signedTotal v eps e) ^ 2) ≤ 1 := by
    simp only [htotal, div_pow, ← mul_div_assoc, ← sum_div_constant]
    exact (div_le_one (sq_pos_of_pos hHpos)).mpr (hmoment eps)
  obtain ⟨eps, b, hb, hcorr⟩ := exists_normalized_signed_correlations μ v (η / H)
    hμ hmass (div_nonneg hη hHpos.le) hvl hvu hnormalized
  refine ⟨b, hb, ?_⟩
  intro i
  have hsign (s : Bool) (x : ℚ) : bitSign s * x ≤ |x| := by
    cases s
    · simpa [bitSign] using neg_le_abs x
    · simpa [bitSign] using le_abs_self x
  have hc := (hcorr i).trans (hsign _ _)
  simp only [v, ← mul_div_assoc, ← sum_div_constant, abs_div, abs_of_pos hHpos] at hc
  have hscale : 3 * (η / H) ^ 2 / 16 = 3 * η ^ 2 / (16 * H) / H := by
    field_simp [ne_of_gt hHpos]
  rw [hscale] at hc
  exact (div_le_div_iff_of_pos_right hHpos).mp hc

#print axioms central_mass
#print axioms abs_boundedSlope_le_one
#print axioms flip_lower_bound
#print axioms exists_normalized_signed_correlations
#print axioms exists_simultaneous_correlation

end HuberCorrelation
