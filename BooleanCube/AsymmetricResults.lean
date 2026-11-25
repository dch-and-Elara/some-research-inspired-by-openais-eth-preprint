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

/-- The two second-order bounds in (5), with separate vanishing errors. -/
theorem asymmetric_second_order_bounds (γ : ℝ) (hγ : 1/2 < γ) :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧
      Tendsto eUpper atTop (𝓝 0) ∧ ∀ q,
        asymmetricLowerEndpoint γ q + eLower q ≤ asymmetricDegreeSquared γ q ∧
        asymmetricDegreeSquared γ q ≤
          (2*γ-1)*Real.log q + Real.log (8/Real.pi) + eUpper q := by
  obtain ⟨e, he, hle⟩ := asymmetric_second_order_lower_error hγ
  let eUpper : ℕ → ℝ := fun q => (symmetricDegree q γ : ℝ)^2/q -
    (2*γ-1)*Real.log q - Real.log (8/Real.pi)
  have hUpper : Tendsto eUpper atTop (𝓝 0) := by
    simpa only [sub_self] using
      (symmetric_degree_asymptotic γ hγ).sub_const (Real.log (8/Real.pi))
  refine ⟨e, eUpper, he, hUpper, fun q => ⟨hle q, ?_⟩⟩
  exact (degreeSquared_le_symmetric q γ).trans_eq (by dsimp [eUpper]; ring)

/-- Theorem C, the leading-order optimum with bit-flip invariance alone. -/
theorem asymmetric_degree_asymptotic (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ => (asymmetricDegree q γ : ℝ)^2 / ((q : ℝ)*Real.log q))
      atTop (𝓝 (2*γ-1)) := by
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
  · filter_upwards [asymmetric_second_order_lower hγ (show (0:ℝ) < 1 by norm_num),
      cube_log_atTop.eventually_gt_atTop 0] with q hq hl
    rw [← div_div]
    exact div_le_div_of_nonneg_right hq hl.le
  · filter_upwards [cube_log_atTop.eventually_gt_atTop 0] with q hl
    rw [← div_div]
    exact div_le_div_of_nonneg_right (degreeSquared_le_symmetric q γ) hl.le

end
end LocalReconstruction

