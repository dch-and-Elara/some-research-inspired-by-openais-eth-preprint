import BooleanCube.AsymmetricLower
import BooleanCube.Symmetric

namespace LocalReconstruction
open Filter
open scoped Topology
noncomputable section

/-- The bit-flip-only optimum is bounded by the symmetric optimum at every dimension. -/
theorem asymmetricDegree_le_symmetricDegree (q : ℕ) (γ : ℝ) :
    asymmetricDegree q γ ≤ symmetricDegree q γ :=
  asymmetricDegree_le_symmetric q γ

private theorem degreeSquared_le_symmetric (q : ℕ) (γ : ℝ) :
    asymmetricDegreeSquared γ q ≤ (symmetricDegree q γ : ℝ)^2/q := by
  unfold asymmetricDegreeSquared
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q)
  have h : (asymmetricDegree q γ : ℝ) ≤ (symmetricDegree q γ : ℝ) := by
    exact_mod_cast (asymmetricDegree_le_symmetricDegree q γ)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2

private theorem two_sided_of_lower_error (γ : ℝ) (hγ : 1/2 < γ) (D : ℕ → ℕ)
    (hu : ∀ q, (D q : ℝ)^2/q ≤ (symmetricDegree q γ : ℝ)^2/q)
    (hLower : ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ q, asymmetricLowerEndpoint γ q + e q ≤ (D q : ℝ)^2/q) :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧ Tendsto eUpper atTop (𝓝 0) ∧
      ∀ q, asymmetricLowerEndpoint γ q + eLower q ≤ (D q : ℝ)^2/q ∧
        (D q : ℝ)^2/q ≤ (2*γ-1)*Real.log q + Real.log (8/Real.pi) + eUpper q := by
  obtain ⟨e,he,hle⟩ := hLower
  let eUpper : ℕ → ℝ := fun q => (symmetricDegree q γ : ℝ)^2/q -
    (2*γ-1)*Real.log q - Real.log (8/Real.pi)
  have hUpper : Tendsto eUpper atTop (𝓝 0) := by
    simpa only [sub_self] using
      (symmetric_degree_asymptotic γ hγ).sub_const (Real.log (8/Real.pi))
  refine ⟨e, eUpper, he, hUpper, fun q => ⟨hle q, ?_⟩⟩
  exact (hu q).trans_eq (by dsimp [eUpper]; ring)

private theorem leading_of_bounds (γ : ℝ) (hγ : 1/2 < γ) (D : ℕ → ℕ)
    (hu : ∀ q, (D q : ℝ)^2/q ≤ (symmetricDegree q γ : ℝ)^2/q)
    (hLower : ∀ᶠ q : ℕ in atTop, asymmetricLowerEndpoint γ q - 1 ≤ (D q : ℝ)^2/q) :
    Tendsto (fun q : ℕ => (D q : ℝ)^2 / ((q : ℝ)*Real.log q)) atTop (𝓝 (2*γ-1)) := by
  let c : ℝ := 2*γ-1
  let sym : ℕ → ℝ := fun q => (symmetricDegree q γ : ℝ)^2/q
  have lower := asymmetric_endpoint_ratio γ 1
  have b := symmetric_degree_asymptotic γ hγ
  change Tendsto (fun q => sym q - c*Real.log q) atTop _ at b
  have u := ((b.mul (tendsto_inv_atTop_zero.comp cube_log_atTop)).const_add c)
  rw [mul_zero, add_zero] at u
  have upper : Tendsto (fun q => sym q / Real.log q) atTop (𝓝 c) := by
    apply u.congr'
    filter_upwards [cube_log_atTop.eventually_gt_atTop 0] with q hl
    change c + (sym q - c*Real.log q) * (Real.log q)⁻¹ = _
    field_simp; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower upper
  · filter_upwards [hLower,
      cube_log_atTop.eventually_gt_atTop 0] with q hq hl
    rw [← div_div]
    exact div_le_div_of_nonneg_right hq hl.le
  · filter_upwards [cube_log_atTop.eventually_gt_atTop 0] with q hl
    rw [← div_div]
    exact div_le_div_of_nonneg_right (hu q) hl.le


/-- The two second-order bounds in (5), with separate vanishing errors. -/
theorem unrestricted_second_order_bounds (ternaryOnly : Bool) (γ : ℝ) (hγ : 1/2 < γ) :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧
      Tendsto eUpper atTop (𝓝 0) ∧ ∀ q,
        asymmetricLowerEndpoint γ q + eLower q ≤ (unrestrictedDegree ternaryOnly q γ : ℝ)^2/q ∧
        (unrestrictedDegree ternaryOnly q γ : ℝ)^2/q ≤
          (2*γ-1)*Real.log q + Real.log (8/Real.pi) + eUpper q :=
  two_sided_of_lower_error γ hγ _ (fun q => (unrestricted_sq_le_asymmetric ternaryOnly q γ).trans (degreeSquared_le_symmetric q γ))
    (unrestricted_second_order_lower_error ternaryOnly hγ)

/-- Theorem C, the leading-order optimum with unrestricted measurement row spaces. -/
theorem unrestricted_degree_asymptotic (ternaryOnly : Bool) (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ => (unrestrictedDegree ternaryOnly q γ : ℝ)^2 / ((q : ℝ)*Real.log q))
      atTop (𝓝 (2*γ-1)) :=
  leading_of_bounds γ hγ _ (fun q => (unrestricted_sq_le_asymmetric ternaryOnly q γ).trans (degreeSquared_le_symmetric q γ))
    (unrestricted_second_order_lower ternaryOnly hγ (by norm_num))

/-- The two second-order bounds in (5), with separate vanishing errors. -/
theorem asymmetric_second_order_bounds (γ : ℝ) (hγ : 1/2 < γ) :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧
      Tendsto eUpper atTop (𝓝 0) ∧ ∀ q,
        asymmetricLowerEndpoint γ q + eLower q ≤ asymmetricDegreeSquared γ q ∧
        asymmetricDegreeSquared γ q ≤
          (2*γ-1)*Real.log q + Real.log (8/Real.pi) + eUpper q :=
  two_sided_of_lower_error γ hγ _ (fun q => degreeSquared_le_symmetric q γ)
    (asymmetric_second_order_lower_error hγ)

/-- Theorem C, the leading-order optimum with bit-flip invariance alone. -/
theorem asymmetric_degree_asymptotic (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ => (asymmetricDegree q γ : ℝ)^2 / ((q : ℝ)*Real.log q))
      atTop (𝓝 (2*γ-1)) :=
  leading_of_bounds γ hγ _ (fun q => degreeSquared_le_symmetric q γ)
    (asymmetric_second_order_lower hγ (by norm_num))

end
end LocalReconstruction
