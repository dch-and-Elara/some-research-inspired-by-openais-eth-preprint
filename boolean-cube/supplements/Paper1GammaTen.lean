import BooleanCube.AsymmetricResults

/-! Paper 1, §8. Specialization to the original exponent-10 row budget. -/
namespace LocalReconstruction.Paper1Coverage

open Filter
open scoped Topology

private theorem original_exponent_admissible : (1/2 : ℝ) < 10 := by norm_num
private theorem original_leading_constant : (2:ℝ) * 10 - 1 = 19 := by norm_num
private theorem original_constant_sq : (19:ℝ)^2 = 361 := by norm_num

theorem original_measurement_budget (q : ℕ) :
    measurementBudget q 10 = (2:ℝ)^q / (q:ℝ)^(10:ℕ) := by
  change (2:ℝ)^q / (q:ℝ)^((10:ℕ):ℝ) = _
  rw [Real.rpow_natCast]

theorem original_symmetric_expansion :
    Tendsto (fun q : ℕ => (symmetricDegree q 10:ℝ)^2/q - 19 * Real.log q)
      atTop (𝓝 (Real.log (8/Real.pi))) := by
  simpa only [original_leading_constant] using
    symmetric_degree_asymptotic 10 original_exponent_admissible

private theorem sqrt_ratio_of_sq_limit (D : ℕ → ℕ)
    (h : Tendsto (fun q : ℕ => (D q : ℝ)^2 / ((q:ℝ)*Real.log q)) atTop (𝓝 19)) :
    Tendsto (fun q : ℕ => (D q : ℝ) / Real.sqrt (19 * ((q:ℝ)*Real.log q))) atTop (𝓝 1) := by
  have h' := (h.div_const (19:ℝ)).sqrt
  have h'' : Tendsto (fun q : ℕ => Real.sqrt (((D q : ℝ)^2 / ((q:ℝ)*Real.log q)) / 19))
      atTop (𝓝 1) := by
    simpa only [div_self (by norm_num : (19:ℝ) ≠ 0), Real.sqrt_one] using h'
  apply h''.congr'
  exact Eventually.of_forall fun q => by
    dsimp only
    rw [div_div, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _), mul_comm (a := (q:ℝ)*Real.log q)]

theorem original_bit_flip_sqrt_asymptotic :
    Tendsto (fun q : ℕ => (asymmetricDegree q 10:ℝ) /
      Real.sqrt (19 * ((q:ℝ)*Real.log q))) atTop (𝓝 1) :=
  sqrt_ratio_of_sq_limit (fun q => asymmetricDegree q 10) (by
    simpa only [original_leading_constant] using
      asymmetric_degree_asymptotic 10 original_exponent_admissible)

/-- Both unrestricted cases in §8, with `true` for ternary and `false` for rational. -/
theorem original_unrestricted_sqrt_asymptotic (ternaryOnly : Bool) :
    Tendsto (fun q : ℕ => (unrestrictedDegree ternaryOnly q 10:ℝ) /
      Real.sqrt (19 * ((q:ℝ)*Real.log q))) atTop (𝓝 1) :=
  sqrt_ratio_of_sq_limit (fun q => unrestrictedDegree ternaryOnly q 10) (by
    simpa only [original_leading_constant] using
      unrestricted_degree_asymptotic ternaryOnly 10 original_exponent_admissible)

theorem original_bit_flip_second_order :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧ Tendsto eUpper atTop (𝓝 0) ∧
      ∀ q : ℕ, 19 * Real.log q - 2 * Real.log (Real.log q) + Real.log (2/(361*Real.pi)) +
          eLower q ≤ (asymmetricDegree q 10:ℝ)^2/q ∧
        (asymmetricDegree q 10:ℝ)^2/q ≤ 19 * Real.log q + Real.log (8/Real.pi) + eUpper q := by
  simpa only [asymmetricLowerEndpoint, asymmetricDegreeSquared, original_leading_constant,
    original_constant_sq, mul_comm Real.pi (361:ℝ)] using
    asymmetric_second_order_bounds 10 original_exponent_admissible

theorem original_unrestricted_second_order (ternaryOnly : Bool) :
    ∃ eLower eUpper : ℕ → ℝ, Tendsto eLower atTop (𝓝 0) ∧ Tendsto eUpper atTop (𝓝 0) ∧
      ∀ q : ℕ, 19 * Real.log q - 2 * Real.log (Real.log q) + Real.log (2/(361*Real.pi)) +
          eLower q ≤ (unrestrictedDegree ternaryOnly q 10:ℝ)^2/q ∧
        (unrestrictedDegree ternaryOnly q 10:ℝ)^2/q ≤
          19 * Real.log q + Real.log (8/Real.pi) + eUpper q := by
  simpa only [asymmetricLowerEndpoint, original_leading_constant,
    original_constant_sq, mul_comm Real.pi (361:ℝ)] using
    unrestricted_second_order_bounds ternaryOnly 10 original_exponent_admissible

end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.original_measurement_budget
#print axioms LocalReconstruction.Paper1Coverage.original_symmetric_expansion
#print axioms LocalReconstruction.Paper1Coverage.original_bit_flip_sqrt_asymptotic
#print axioms LocalReconstruction.Paper1Coverage.original_unrestricted_sqrt_asymptotic
#print axioms LocalReconstruction.Paper1Coverage.original_bit_flip_second_order
#print axioms LocalReconstruction.Paper1Coverage.original_unrestricted_second_order
