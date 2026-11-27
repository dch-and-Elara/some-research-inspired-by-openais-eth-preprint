import PublicSparseRun
import IndexedExecutionCharge

/-! The external-execution clause of Theorem 4 (Appendix C).
The ordered realization in an external execution is an input witness.
Only the charged-step lower bound is transferred, not solver correctness. -/

noncomputable section

namespace RootSeparation.Preprocessing

open Entry S11 GraphCutMoments Solver
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The published count and digit bound concern the same returned sparse
trace. For any external indexed run, an order-preserving injection from those
digit positions, with at least one unit charged at each image, transfers the
same real-valued lower bound to the sum of all external charges. -/
theorem publicSparseRun_count_and_external_work (E : Finset (V × V)) (simple : Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (large : sizeCutoff < n (V := V)) :
    dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse ∧
      ∃ trace, publicSparseRun E reg σ =
          some (PinnedCNF.modelCount (PinnedCNF.formula E σ), trace) ∧
        (2 : ℝ)^((n (V := V) : ℝ) / (2 * Real.sqrt (Real.logb 2 (n (V := V))))) ≤
          ((Execution.executedDigits trace).length : ℝ) ∧
        ∀ (steps : ℕ) (charge : Fin steps → ℕ)
          (embed : Fin (Execution.executedDigits trace).length → Fin steps),
          StrictMono embed → (∀ i, 1 ≤ charge (embed i)) →
          (2 : ℝ)^((n (V := V) : ℝ) / (2 * Real.sqrt (Real.logb 2 (n (V := V))))) ≤
            ((∑ j, charge j : ℕ) : ℝ) := by
  obtain ⟨hdispatch, trace, htrace, hdigits⟩ := publicSparseRun_count_and_work E simple reg σ large
  refine ⟨hdispatch, trace, htrace, hdigits, ?_⟩
  intro steps charge embed horder hunit
  have h := IndexedExecutionCharge.embedded_count_le_charge charge embed horder.injective hunit
  exact hdigits.trans (by exact_mod_cast h)

#print axioms publicSparseRun_count_and_external_work

end RootSeparation.Preprocessing
