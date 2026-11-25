import BooleanCube.RealBudget

namespace LocalReconstruction

/-- Minimum admissible degree with the original real measurement budget. -/
noncomputable def symmetricDegree (q : ℕ) (γ : ℝ) : ℕ :=
  sInf {d | realSymmetricScheme q d γ}

theorem exists_optimal_symmetric_layers (q : ℕ) (γ : ℝ) :
    ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧
      ((∑ k ∈ K, q.choose k : ℕ) : ℝ) ≤ measurementBudget q γ ∧
      maxGap q K = symmetricDegree q γ := by
  have hn : 0 ≤ measurementBudget q γ :=
    div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [symmetricDegree, symmetric_exact_real_budget]
  have hne : ({g | ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧
      ((∑ k ∈ K, q.choose k : ℕ) : ℝ) ≤ measurementBudget q γ ∧
      g = maxGap q K} : Set ℕ).Nonempty :=
    ⟨maxGap q ∅, ∅, Finset.empty_subset _, by simpa using hn, rfl⟩
  obtain ⟨K, hK, hb, hg⟩ := Nat.sInf_mem hne
  exact ⟨K, hK, hb, hg.symm⟩

theorem symmetricDegree_le_maxGap {q : ℕ} {γ : ℝ} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (q+1))
    (hb : ((∑ k ∈ K, q.choose k : ℕ) : ℝ) ≤ measurementBudget q γ) :
    symmetricDegree q γ ≤ maxGap q K := by
  rw [symmetricDegree, symmetric_exact_real_budget]
  exact Nat.sInf_le ⟨K, hK, hb, rfl⟩

/-- The minimum is attained by a scheme in the original matrix formulation. -/
theorem realSymmetricScheme_symmetricDegree (q : ℕ) (γ : ℝ) :
    realSymmetricScheme q (symmetricDegree q γ) γ := by
  obtain ⟨K, hK, hb, hg⟩ := exists_optimal_symmetric_layers q γ
  let a : Fin q → ℚ := fun i => ((i.val+1:ℕ):ℚ)
  have hi : Function.Injective a := by
    intro i j h
    apply Fin.ext
    change ((i.val+1:ℕ):ℚ) = ((j.val+1:ℕ):ℚ) at h
    exact Nat.add_right_cancel (by exact_mod_cast h : i.val+1 = j.val+1)
  have ha (i : Fin q) : a i ≠ 0 := by dsimp [a]; positivity
  have hp : 0 ≤ measurementBudget q γ :=
    div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hs : symmetricScheme q ⌊measurementBudget q γ⌋₊ (symmetricDegree q γ) a :=
    (symmetric_budget_iff hi ha).mpr ⟨K, hK, (Nat.le_floor_iff hp).mpr hb,
      (maxGap_le_iff _ _ _).mp hg.le⟩
  simpa only [symmetricScheme, realSymmetricScheme, Nat.le_floor_iff hp, a] using hs

theorem symmetricDegree_le_of_scheme {q d : ℕ} {γ : ℝ}
    (h : realSymmetricScheme q d γ) : symmetricDegree q γ ≤ d :=
  Nat.sInf_le h

end LocalReconstruction
