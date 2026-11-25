import BooleanCube.MatrixCertificates

namespace LocalReconstruction
noncomputable section

/-- No row-space invariance. With ternaryOnly = false every rational matrix is allowed. -/
def unrestrictedScheme (ternaryOnly : Bool) (q d : ℕ) (γ : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ measurementBudget q γ ∧
    ∃ M : Matrix (Fin m) (Cube q) ℚ, (ternaryOnly = true → Ternary M) ∧
      ∃ P, matrixCondition (fun i => ((i.val + 1 : ℕ) : ℚ)) M d P

def unrestrictedDegree (ternaryOnly : Bool) (q : ℕ) (γ : ℝ) : ℕ :=
  sInf {d | unrestrictedScheme ternaryOnly q d γ}

theorem realAsymmetricScheme.unrestricted {q d : ℕ} {γ : ℝ}
    (h : realAsymmetricScheme q d γ) (ternaryOnly : Bool) :
    unrestrictedScheme ternaryOnly q d γ := by
  obtain ⟨m,hm,M,ht,_,hP⟩ := h
  exact ⟨m,hm,M,fun _ => ht,hP⟩

theorem unrestrictedDegree_feasible (ternaryOnly : Bool) (q : ℕ) (γ : ℝ) :
    unrestrictedScheme ternaryOnly q (unrestrictedDegree ternaryOnly q γ) γ :=
  Nat.sInf_mem (s := {d | unrestrictedScheme ternaryOnly q d γ})
    ⟨q, (realSymmetricScheme_at_dimension q γ).asymmetric.unrestricted ternaryOnly⟩

theorem unrestrictedDegree_le_asymmetric (ternaryOnly : Bool) (q : ℕ) (γ : ℝ) :
    unrestrictedDegree ternaryOnly q γ ≤ asymmetricDegree q γ :=
  Nat.sInf_le ((asymmetricDegree_feasible q γ).unrestricted ternaryOnly)

theorem unrestricted_bilinear_budget {ternaryOnly : Bool} {q d r K : ℕ} {γ : ℝ}
    (h : unrestrictedScheme ternaryOnly q d γ) (hr : d+r < q) (hK : K ≤ r) :
    (∑ j ∈ Finset.range (K+1), ∑ l ∈ Finset.range (min j (r-j)+1),
      (q.choose l : ℝ)) ≤ (K+1 : ℕ) * measurementBudget q γ := by
  obtain ⟨m, hm, M, _, P, hp⟩ := h
  let a : Fin q → ℚ := fun i => ((i.val + 1 : ℕ) : ℚ)
  have hi : Function.Injective a := by
    intro i j hij
    apply Fin.ext
    change ((i.val + 1 : ℕ) : ℚ) = ((j.val + 1 : ℕ) : ℚ) at hij
    exact Nat.add_right_cancel (by exact_mod_cast hij)
  have hn (i : Fin q) : a i ≠ 0 := by dsimp [a]; positivity
  have hb := matrix_bilinear_budget hi hn hp hr hK
  calc
    _ ≤ ((K+1 : ℕ) : ℝ) * (m : ℝ) := by exact_mod_cast hb
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

end
end LocalReconstruction
