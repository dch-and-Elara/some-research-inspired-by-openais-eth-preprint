import BooleanCube.Budget
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LocalReconstruction
noncomputable section

def measurementBudget (q : ℕ) (γ : ℝ) : ℝ := (2:ℝ)^q / (q:ℝ)^γ

def realSymmetricScheme (q d : ℕ) (γ : ℝ) : Prop :=
  ∃ m : ℕ, (m:ℝ) ≤ measurementBudget q γ ∧
    ∃ C : Matrix (Fin m) (Cube q) ℚ, Ternary C ∧ FlipInvariant (rowSpace C) ∧
      PermInvariant (rowSpace C) ∧ ∃ P, matrixCondition (fun i => ((i.val+1:ℕ):ℚ)) C d P

/-- The original real budget on both matrices and deleted layer costs. -/
theorem symmetric_exact_real_budget (q : ℕ) (γ : ℝ) :
    sInf {d | realSymmetricScheme q d γ} =
      sInf {g | ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧
        ((∑ k ∈ K, q.choose k : ℕ) : ℝ) ≤ measurementBudget q γ ∧ g = maxGap q K} := by
  have hn : 0 ≤ measurementBudget q γ := by
    exact div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg q) γ)
  simpa only [symmetricScheme,realSymmetricScheme,affordableGaps,Nat.le_floor_iff hn] using
    symmetric_exact_integer_budget q ⌊measurementBudget q γ⌋₊

end
end LocalReconstruction
