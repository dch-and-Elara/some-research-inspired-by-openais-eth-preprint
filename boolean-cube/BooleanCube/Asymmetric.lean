import BooleanCube.RealBudget
import BooleanCube.BilinearBudget

namespace LocalReconstruction
open Polynomial
open scoped Polynomial
noncomputable section

/-- Feasibility for the original rational reconstruction matrix and ternary
measurements. Only the measurement row space is required to be flip-invariant. -/
def realAsymmetricScheme (q d : ℕ) (γ : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ measurementBudget q γ ∧
    ∃ C : Matrix (Fin m) (Cube q) ℚ, Ternary C ∧ FlipInvariant (rowSpace C) ∧
      ∃ P, matrixCondition (fun i => ((i.val + 1 : ℕ) : ℚ)) C d P

/-- Minimum feasible degree for bit-flip invariant ternary measurements. -/
def asymmetricDegree (q : ℕ) (γ : ℝ) : ℕ :=
  sInf {d | realAsymmetricScheme q d γ}

theorem realSymmetricScheme.asymmetric {q d : ℕ} {γ : ℝ}
    (h : realSymmetricScheme q d γ) : realAsymmetricScheme q d γ := by
  obtain ⟨m, hm, C, ht, hf, _, hP⟩ := h
  exact ⟨m, hm, C, ht, hf, hP⟩

theorem realSymmetricScheme_at_dimension (q : ℕ) (γ : ℝ) : realSymmetricScheme q q γ := by
  classical
  let a : Fin q → ℚ := fun i => ((i.val + 1 : ℕ) : ℚ)
  let f : ℚ[X] := ∏ i, (1 - C (a i)⁻¹ * X)
  refine ⟨0, ?_, 0, ?_, ?_, ?_, fun u v => if u = v then f else 0, ?_⟩
  · simp only [Nat.cast_zero, measurementBudget]
    exact div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg q) γ)
  · intro i
    exact Fin.elim0 i
  · intro i g hg
    have hg0 : g = 0 := by simpa [rowSpace, Set.range_eq_empty] using hg
    rw [hg0]
    exact (rowSpace (0 : Matrix (Fin 0) (Cube q) ℚ)).zero_mem
  · intro e g hg
    have hg0 : g = 0 := by simpa [rowSpace, Set.range_eq_empty] using hg
    rw [hg0]
    exact (rowSpace (0 : Matrix (Fin 0) (Cube q) ℚ)).zero_mem
  · refine ⟨?_, ?_, ?_⟩
    · intro u v
      change (if u = v then f else 0).natDegree ≤ q
      split_ifs
      · apply (natDegree_prod_le ..).trans
        calc
          _ ≤ ∑ _i : Fin q, 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact (natDegree_sub_le ..).trans
              (max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp)))
          _ = q := by simp
      · simp
    · intro u v
      change eval 0 (if u = v then f else 0) = _
      by_cases h : u = v <;> simp [h, f, eval_prod]
    · intro u i h _ _
      have ha : a i ≠ 0 := by dsimp [a]; positivity
      have hf : f.eval (a i) = 0 := by
        rw [show f = ∏ j, (1 - C (a j)⁻¹ * X) from rfl, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [ha])
      apply Finset.sum_eq_zero
      intro v _
      change (eval (a i) (if u = v then f else 0)) * h v = 0
      split_ifs <;> simp [hf]

theorem asymmetricDegree_feasible (q : ℕ) (γ : ℝ) :
    realAsymmetricScheme q (asymmetricDegree q γ) γ :=
  Nat.sInf_mem (s := {d | realAsymmetricScheme q d γ})
    ⟨q, (realSymmetricScheme_at_dimension q γ).asymmetric⟩

theorem asymmetricDegree_le_symmetric (q : ℕ) (γ : ℝ) :
    asymmetricDegree q γ ≤ sInf {d | realSymmetricScheme q d γ} :=
  Nat.sInf_le (realSymmetricScheme.asymmetric
    (Nat.sInf_mem (s := {d | realSymmetricScheme q d γ}) ⟨q, realSymmetricScheme_at_dimension q γ⟩))

theorem asymmetricDegree_le_dimension (q : ℕ) (γ : ℝ) : asymmetricDegree q γ ≤ q :=
  Nat.sInf_le (realSymmetricScheme_at_dimension q γ).asymmetric

/-- Finite inequality (23) for a feasible ternary measurement matrix. -/
theorem asymmetric_bilinear_budget {q d r K : ℕ} {γ : ℝ}
    (h : realAsymmetricScheme q d γ) (hr : d + r < q) (hK : K ≤ r) :
    (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (min j (r-j)+1),
      (q.choose l : ℝ)) ≤ (K+1 : ℕ) * measurementBudget q γ := by
  classical
  obtain ⟨m, hm, C, _, hf, hP⟩ := h
  obtain ⟨S, hS⟩ := (flipInvariant_iff (rowSpace C)).mp hf
  let A := S.toFinset
  have hA : (↑A : Set (Cube q)) = S := Set.coe_toFinset S
  have heq : rowSpace C = walshSpace (↑A : Set (Cube q)) := hA.symm ▸ hS
  let a : Fin q → ℚ := fun i => ((i.val + 1 : ℕ) : ℚ)
  obtain ⟨p, hp⟩ := (matrix_iff_edges a C _ heq).mp hP
  have hi : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    change ((i.val + 1 : ℕ) : ℚ) = ((j.val + 1 : ℕ) : ℚ) at hij
    exact Nat.add_right_cancel (by exact_mod_cast hij)
  have hn (i : Fin q) : a i ≠ 0 := by dsimp [a]; positivity
  have hcard : A.card ≤ m := by
    have hind : LinearIndependent ℚ (fun s : ↥A => walsh s.val) :=
      (walsh_independent q).comp _ Subtype.val_injective
    have hspan : Submodule.span ℚ (Set.range fun s : ↥A => walsh s.val) = rowSpace C := by
      rw [heq, walshSpace]
      congr 1
      ext f
      simp
    have hdim := finrank_span_eq_card hind
    rw [hspan, Fintype.card_coe] at hdim
    rw [← hdim]
    simpa [rowSpace] using finrank_range_le_card (R := ℚ) C
  have hb := bilinear_budget hi hn A hp hr hK
  calc
    _ ≤ ((K+1 : ℕ) : ℝ) * (A.card : ℝ) := by exact_mod_cast hb
    _ ≤ _ := mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hcard).trans hm) (by positivity)

end
end LocalReconstruction

