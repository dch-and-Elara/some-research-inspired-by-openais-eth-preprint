import BooleanCube.Certificates

/-! Paper 1, §5.2, equation (18).  The ambient spline space and the cube
index are the ones in the public BooleanCube development at 95ad3fb52aeac8376. -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial
open scoped BigOperators
noncomputable section

/-- Restrict the genuine bounded-degree spline to the deleted vertices. -/
def restrictDeleted {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    splines a k →ₗ[ℚ] (↥A → Bounded (k+1)) :=
  LinearMap.pi fun x => (LinearMap.proj (R := ℚ) x.val).comp (splines a k).subtype

/-- The paper's `I_k` inside `H_k`.  There is no reconstruction hypothesis. -/
def vanishingSplines {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    Submodule ℚ (splines a k) :=
  LinearMap.ker (restrictDeleted a k A)

theorem mem_vanishingSplines_iff {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : splines a k) :
    h ∈ vanishingSplines a k A ↔ ∀ x ∈ A, (h.val x).val = 0 := by
  change restrictDeleted a k A h = 0 ↔ _
  constructor
  · intro hh x hx
    exact congrArg Subtype.val (congrFun hh (⟨x, hx⟩ : ↥A))
  · intro hh
    funext x
    exact Subtype.ext (hh x.val x.property)

/-- The genuine restriction target is a product with exactly one factor for
every deleted vertex, each factor having `k+1` free coefficients. -/
theorem restriction_target_finrank {q : ℕ} (k : ℕ) (A : Finset (Cube q)) :
    Module.finrank ℚ (↥A → Bounded (k+1)) = (k+1)*A.card := by
  have h : Module.finrank ℚ (Bounded (k+1)) = k+1 := by
    simpa using (degreeLTEquiv ℚ (k+1)).finrank_eq
  simp [Module.finrank_pi_fintype, h, Nat.mul_comm]

/-- General restriction-kernel dimension. This does not even require distinct
labels. The signed inequality retains the paper's untruncated subtraction. -/
theorem restriction_kernel_dimension {q : ℕ} (a : Fin q → ℚ)
    (k : ℕ) (A : Finset (Cube q)) :
    (Module.finrank ℚ (splines a k) : ℤ) - ((k+1)*A.card : ℕ) ≤
      (Module.finrank ℚ (vanishingSplines a k A) : ℤ) := by
  let T := restrictDeleted a k A
  have rankNull := LinearMap.finrank_range_add_finrank_ker (K := ℚ)
    (V := ↥(splines a k)) (V₂ := (↥A → Bounded (k+1))) T
  have rankLe : Module.finrank ℚ (LinearMap.range T) ≤ Module.finrank ℚ (↥A → Bounded (k+1)) :=
    (LinearMap.range T).finrank_le
  rw [restriction_target_finrank] at rankLe
  change (Module.finrank ℚ (splines a k) : ℤ) - ((k+1)*A.card : ℕ) ≤
      (Module.finrank ℚ (LinearMap.ker T) : ℤ)
  omega

/-- Equation (18), with the binomial expression (17) substituted for `N_q(k)`.
There is no `P`, degree-feasibility, or measurement-row constraint. -/
theorem restriction_kernel_dimension_eq18 {q : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (k : ℕ) (A : Finset (Cube q)) :
    ((∑ j ∈ Finset.range (q+1), (k+1-j)*q.choose j : ℕ) : ℤ) -
      ((k+1)*A.card : ℕ) ≤ (Module.finrank ℚ (vanishingSplines a k A) : ℤ) := by
  rw [← spline_dimension (k := k) ha]
  exact restriction_kernel_dimension a k A

/-- The printed labels are exactly `1,…,q`, viewed as rational numbers. -/
def printedLabels (q : ℕ) : Fin q → ℚ := fun i => ((i.val+1 : ℕ) : ℚ)

theorem printedLabels_injective (q : ℕ) : Function.Injective (printedLabels q) := by
  intro i j hij
  apply Fin.ext
  change ((i.val+1 : ℕ) : ℚ) = ((j.val+1 : ℕ) : ℚ) at hij
  exact Nat.add_right_cancel (by exact_mod_cast hij)

theorem printedLabels_nonzero {q : ℕ} (i : Fin q) : printedLabels q i ≠ 0 := by
  unfold printedLabels
  positivity

/-- The paper's original label specialization, for every deleted family. -/
theorem printed_restriction_kernel_dimension_eq18 (q k : ℕ) (A : Finset (Cube q)) :
    ((∑ j ∈ Finset.range (q+1), (k+1-j)*q.choose j : ℕ) : ℤ) -
      ((k+1)*A.card : ℕ) ≤
        (Module.finrank ℚ (vanishingSplines (printedLabels q) k A) : ℤ) :=
  restriction_kernel_dimension_eq18 (printedLabels_injective q) k A

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.mem_vanishingSplines_iff
#print axioms LocalReconstruction.Paper1Coverage.restriction_target_finrank
#print axioms LocalReconstruction.Paper1Coverage.restriction_kernel_dimension
#print axioms LocalReconstruction.Paper1Coverage.restriction_kernel_dimension_eq18
#print axioms LocalReconstruction.Paper1Coverage.printedLabels_injective
#print axioms LocalReconstruction.Paper1Coverage.printedLabels_nonzero
#print axioms LocalReconstruction.Paper1Coverage.printed_restriction_kernel_dimension_eq18
