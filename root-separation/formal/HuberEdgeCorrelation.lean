import HuberCorrelation

/-! Simultaneous correlation when each function has a lower second moment.
This form applies to cut differences taking the values -1, 0, and 1. -/

namespace HuberEdgeCorrelation

open scoped BigOperators
open BangCore (bitSign signedTotal)
open HuberPotential (rho)
open HuberCorrelation (boundedSlope centralIndicator)

variable {E I : Type*} [Fintype E] [Fintype I]

/-- The finite second-moment tail estimate at threshold two. -/
theorem four_mul_outside_mass_le (μ w : E → ℚ) (hμ : ∀ e, 0 ≤ μ e) :
    4 * (∑ e, μ e * (1 - centralIndicator (w e))) ≤ ∑ e, μ e * w e ^ 2 := by
  have hpoint (x : ℚ) : 4 * (1 - centralIndicator x) ≤ x ^ 2 := by
    by_cases hl : -2 ≤ x
    · by_cases hu : x ≤ 2
      · simpa [centralIndicator, hl, hu] using sq_nonneg x
      · simp only [centralIndicator, hu, and_false, if_false, sub_zero, mul_one]
        nlinarith [sq_nonneg (x - 2)]
    · simp only [centralIndicator, hl, false_and, if_false, sub_zero, mul_one]
      nlinarith [sq_nonneg (x + 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  calc
    4 * (μ e * (1 - centralIndicator (w e))) = μ e * (4 * (1 - centralIndicator (w e))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpoint (w e)) (hμ e)

/-- A bounded function of second moment at least p keeps at least 3p/4 of
that moment on the central interval whenever the second moment of w is at most p. -/
theorem central_energy_lower_bound (μ f w : E → ℚ) (p : ℚ) (hμ : ∀ e, 0 ≤ μ e)
    (habs : ∀ e, |f e| ≤ 1) (henergy : p ≤ ∑ e, μ e * f e ^ 2)
    (hmoment : (∑ e, μ e * w e ^ 2) ≤ p) :
    3 * p / 4 ≤ ∑ e, μ e * f e ^ 2 * centralIndicator (w e) := by
  have hpoint (e : E) :
      f e ^ 2 - f e ^ 2 * centralIndicator (w e) ≤ 1 - centralIndicator (w e) := by
    by_cases hc : -2 ≤ w e ∧ w e ≤ 2
    · simp [centralIndicator, hc]
    · have h := (sq_le_sq₀ (abs_nonneg (f e)) zero_le_one).mpr (habs e)
      simpa [centralIndicator, hc] using h
  have hloss : (∑ e, μ e * f e ^ 2) - (∑ e, μ e * f e ^ 2 * centralIndicator (w e)) ≤
      ∑ e, μ e * (1 - centralIndicator (w e)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    linarith only [mul_le_mul_of_nonneg_left (hpoint e) (hμ e)]
  linarith only [henergy, hmoment, hloss, four_mul_outside_mass_le μ w hμ]

private theorem scaled_flip (x a H : ℚ) (s : Bool) (hH : 1 ≤ H) (ha : |a| ≤ 1) :
    -8 * H * bitSign s * (boundedSlope x * a) + 2 * a ^ 2 * centralIndicator x ≤
      H ^ 2 * (rho (x - 2 * bitSign s * a / H) - rho x) := by
  have hp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hbound : |a / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hp, div_le_one hp]
    exact ha.trans hH
  have h := HuberCorrelation.flip_lower_bound x (a / H) |a / H| s
    (abs_nonneg _) le_rfl hbound
  rw [sq_abs] at h
  calc
    _ = H ^ 2 * (-8 * bitSign s * (boundedSlope x * (a / H)) +
        2 * (a / H) ^ 2 * centralIndicator x) := by
      field_simp [ne_of_gt hp]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg H)
    _ = _ := by rw [← mul_div_assoc]

/-- A single maximizing sign vector captures the central energy of every
function. This comparison does not require any lower bound on the functions. -/
theorem exists_signs_for_central_energy (μ : E → ℚ) (f : I → E → ℚ) (H : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hH : 1 ≤ H) (habs : ∀ i e, |f i e| ≤ 1) :
    ∃ eps : I → Bool, ∀ i,
      (∑ e, μ e * f i e ^ 2 * centralIndicator (signedTotal f eps e / H)) ≤
        4 * H * bitSign (eps i) *
          ∑ e, μ e * boundedSlope (signedTotal f eps e / H) * f i e := by
  classical
  let objective (eps : I → Bool) := ∑ e, μ e * rho (signedTotal f eps e / H)
  obtain ⟨eps, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (I → Bool)) objective Finset.univ_nonempty
  let w (e : E) := signedTotal f eps e / H
  refine ⟨eps, ?_⟩
  intro i
  let r := bitSign (eps i)
  have hflip : (∑ e, μ e * rho (w e - 2 * r * f i e / H)) ≤
      ∑ e, μ e * rho (w e) := by
    have h := hmax (Function.update eps i (!(eps i))) (Finset.mem_univ _)
    dsimp only [objective] at h
    rw [BangCore.flip_identity] at h
    simpa only [sub_div] using h
  have hsum : -8 * H * r * (∑ e, μ e * boundedSlope (w e) * f i e) +
      2 * (∑ e, μ e * f i e ^ 2 * centralIndicator (w e)) ≤
        H ^ 2 * ((∑ e, μ e * rho (w e - 2 * r * f i e / H)) - ∑ e, μ e * rho (w e)) := by
    rw [mul_sub]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro e _
    have h := mul_le_mul_of_nonneg_left
      (scaled_flip (w e) (f i e) H (eps i) hH (habs i e)) (hμ e)
    dsimp only [r]
    linarith only [h]
  change (∑ e, μ e * f i e ^ 2 * centralIndicator (w e)) ≤
    4 * H * r * ∑ e, μ e * boundedSlope (w e) * f i e
  linarith only [hsum, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg H) (sub_nonpos.mpr hflip)]

/-- If each function has second moment at least p and all signed sums have
second moment at most pH², there is one bounded rational witness of correlation
at least 3p/(16H) with each function. Finite nonnegative weights suffice. -/
theorem exists_simultaneous_edge_correlation (μ : E → ℚ) (f : I → E → ℚ) (p H : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hH : 1 ≤ H) (habs : ∀ i e, |f i e| ≤ 1)
    (henergy : ∀ i, p ≤ ∑ e, μ e * f i e ^ 2)
    (hmoment : ∀ eps : I → Bool, (∑ e, μ e * (signedTotal f eps e) ^ 2) ≤ p * H ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧
        ∀ i, 3 * p / (16 * H) ≤ |∑ e, μ e * b e * f i e| := by
  obtain ⟨eps, hc⟩ := exists_signs_for_central_energy μ f H hμ hH habs
  let w (e : E) := signedTotal f eps e / H
  have hp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hw : (∑ e, μ e * w e ^ 2) ≤ p := by
    have hscale : (∑ e, μ e * w e ^ 2) = (∑ e, μ e * (signedTotal f eps e) ^ 2) / H ^ 2 := by
      simp only [w, div_pow, ← mul_div_assoc]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [hscale, div_le_iff₀ (sq_pos_of_pos hp)]
    exact hmoment eps
  refine ⟨fun e => boundedSlope (w e), fun e => HuberCorrelation.abs_boundedSlope_le_one _, ?_⟩
  intro i
  have hm := central_energy_lower_bound μ (f i) w p hμ (habs i) (henergy i) hw
  have hs := hm.trans (hc i)
  let c := ∑ e, μ e * boundedSlope (w e) * f i e
  have hsigned : 3 * p / (16 * H) ≤ bitSign (eps i) * c := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hp)]
    change 3 * p / 4 ≤ 4 * H * bitSign (eps i) * c at hs
    linarith only [hs]
  apply hsigned.trans
  change bitSign (eps i) * c ≤ |c|
  cases eps i
  · simpa [bitSign] using neg_le_abs c
  · simpa [bitSign] using le_abs_self c

/-- If the signed edge sums have second moment at most (2A)², the rational
choice H = 2A/p gives the bound 3p²/(32A). -/
theorem exists_edge_correlation_of_doubled_bound (μ : E → ℚ) (f : I → E → ℚ) (p A : ℚ)
    (hμ : ∀ e, 0 ≤ μ e) (hp : 0 < p) (hp1 : p ≤ 1) (hA : 1 ≤ A)
    (habs : ∀ i e, |f i e| ≤ 1) (henergy : ∀ i, p ≤ ∑ e, μ e * f i e ^ 2)
    (hmoment : ∀ eps : I → Bool, (∑ e, μ e * (signedTotal f eps e) ^ 2) ≤ (2 * A) ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧
        ∀ i, 3 * p ^ 2 / (32 * A) ≤ |∑ e, μ e * b e * f i e| := by
  have hH : 1 ≤ 2 * A / p := by
    rw [le_div_iff₀ hp]
    linarith
  have hscale : (2 * A) ^ 2 ≤ p * (2 * A / p) ^ 2 := by
    have hid : p * (2 * A / p) ^ 2 = (2 * A) ^ 2 / p := by field_simp
    rw [hid, le_div_iff₀ hp]
    simpa using mul_le_mul_of_nonneg_left hp1 (sq_nonneg (2 * A))
  obtain ⟨b, hb, hc⟩ := exists_simultaneous_edge_correlation μ f p (2 * A / p)
    hμ hH habs henergy (fun eps => (hmoment eps).trans hscale)
  refine ⟨b, hb, ?_⟩
  intro i
  have hconstant : 3 * p / (16 * (2 * A / p)) = 3 * p ^ 2 / (32 * A) := by
    have ha : 0 < A := lt_of_lt_of_le zero_lt_one hA
    field_simp [ne_of_gt hp, ne_of_gt ha]
    ring
  simpa only [hconstant] using hc i

#print axioms four_mul_outside_mass_le
#print axioms central_energy_lower_bound
#print axioms exists_signs_for_central_energy
#print axioms exists_simultaneous_edge_correlation
#print axioms exists_edge_correlation_of_doubled_bound

end HuberEdgeCorrelation
