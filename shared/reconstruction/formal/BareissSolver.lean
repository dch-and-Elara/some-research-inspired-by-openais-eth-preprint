import BareissSolverCorrect
import BareissHeight

/-!
# Generic rational Gaussian elimination

`solveIntScaled` and `solveInt` take an integer augmented matrix. Column
`none` is the right-hand side. `solve` clears the denominators of an
arbitrary rational system and runs the same deterministic elimination.
-/

namespace Reconstruction.BareissSolver

def solveIntScaled {m n : ℕ} (Z : IntegerAugment m n) : Run n :=
  runInt m n (denseAugment Z) 1

def solveInt {m n : ℕ} (Z : IntegerAugment m n) : Option (Column n) :=
  (solveIntScaled Z).result.map ScaledSolution.rational

abbrev clear {m n : ℕ} (A : Coefficients m n) (b : Column m) : IntegerAugment m n :=
  BareissHeight.clearRows (BareissHeight.augment A b)

def solve {m n : ℕ} (A : Coefficients m n) (b : Column m) : Option (Column n) :=
  solveInt (clear A b)

theorem solveIntScaled_operations {m n : ℕ} (Z : IntegerAugment m n) :
    (solveIntScaled Z).operations ≤ (min m n+1)*stageBudget m n :=
  runInt_operations m n (denseAugment Z) 1

theorem solveInt_refines {m n : ℕ} (Z : IntegerAugment m n) :
    solveInt Z = solveCore m n (integerCoefficients Z) (integerRhs Z) :=
  (runInt_correct m n 0 1 (integerCoefficients Z) (integerRhs Z) (denseAugment Z)
    (MinorFrame.initial Z) (represents_initial Z)).1

theorem solveIntScaled_spec {m n : ℕ} (Z : IntegerAugment m n) :
    ((solveIntScaled Z).result.isSome ↔ ∃ x, Solves (integerCoefficients Z) (integerRhs Z) x) ∧
    ∀ s, (solveIntScaled Z).result = some s →
      Solves (integerCoefficients Z) (integerRhs Z) s.rational ∧ s.denominator ≠ 0 ∧
      ∃ k ≤ min m n, HasMinor Z k s.denominator ∧
        ∀ j, s.numerator j = 0 ∨ HasMinor Z k (s.numerator j) := by
  have h := runInt_correct m n 0 1 (integerCoefficients Z) (integerRhs Z) (denseAugment Z)
    (MinorFrame.initial Z) (represents_initial Z)
  have hsome := congrArg Option.isSome h.1
  rw [Option.isSome_map] at hsome
  refine ⟨?_, ?_⟩
  · change ((runInt m n (denseAugment Z) 1).result.isSome = true ↔ _)
    rw [hsome]
    exact (solveCore_spec ..).1
  · intro s hs
    have hv := h.2 s hs
    exact ⟨hv.solves,hv.nonzero,by simpa only [zero_add] using hv.minors (MinorFrame.initial Z)⟩

theorem solves_clear_iff {m n : ℕ} (A : Coefficients m n) (b : Column m) (x : Column n) :
    Solves (integerCoefficients (clear A b)) (integerRhs (clear A b)) x ↔ Solves A b x := by
  simpa only [Solves, integerCoefficients_apply, integerRhs_apply, clear] using
    BareissHeight.clearRows_system_iff A b x

/-- Completeness requires only consistency. Every returned vector solves
the original rational system. -/
theorem solve_spec {m n : ℕ} (A : Coefficients m n) (b : Column m) :
    ((solve A b).isSome ↔ ∃ x, Solves A b x) ∧
      (∀ x, solve A b = some x → Solves A b x) := by
  rw [solve, solveInt_refines]
  have h := solveCore_spec m n (integerCoefficients (clear A b)) (integerRhs (clear A b))
  constructor
  · simpa only [solves_clear_iff] using h.1
  · intro x hx
    exact (solves_clear_iff A b x).mp (h.2 x hx)

theorem solve_exists_of_consistent {m n : ℕ} (A : Coefficients m n) (b : Column m)
    (h : ∃ x, A.mulVec x = b) : ∃ x, solve A b = some x ∧ A.mulVec x = b := by
  have hz : (solve A b).isSome := (solve_spec A b).1.mpr (by simpa only [solves_iff_mulVec] using h)
  cases hx : solve A b with
  | none => simp [hx] at hz
  | some x => exact ⟨x,rfl,solves_iff_mulVec.mp ((solve_spec A b).2 x hx)⟩

end Reconstruction.BareissSolver
