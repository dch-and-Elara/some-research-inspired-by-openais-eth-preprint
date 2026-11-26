import PreprocessingThresholds
import SolverPinnedCorrectness

noncomputable section

namespace RootSeparation.Preprocessing

open Entry S11 GraphCutMoments Solver

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The existing sparse dispatcher, with the solver's polynomial choice and
coordinate zero. Decode the value and retain the trace from the same result. -/
def publicSparseRun (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) : Option (ℕ × List Execution.Step) := by
  classical
  exact if ep : 0 < 4 * lambda (size E) then
    let F := Classical.choice (sourcePolynomial_exists _ ep)
    (runPinnedSparse E reg σ F ⟨0, ep⟩).map fun r =>
      (rootConstant E F ep r.value, r.localTrace)
  else none

theorem publicSparseRun_count_projection (E : Finset (V × V))
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (hn : 20 ≤ n (V := V)) :
    (publicSparseRun E reg σ).map Prod.fst = solveUnclonedPinned E reg σ hn := by
  rw [publicSparseRun, dif_pos (coefficient_degree_pos E hn), Option.map_map]
  rfl

theorem publicSparse_log_gate (E : Finset (V × V)) (large : sizeCutoff < n (V := V)) :
    2^40 ≤ lambda (size E) := by
  have h : 2^40 ≤ depthLogCutoff := by
    unfold depthLogCutoff
    decide
  exact h.trans (eventual_log E large)

theorem publicSparseRun_active (E : Finset (V × V)) (simple : Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (large : sizeCutoff < n (V := V)) :
    let hn := sizeCutoff_bigRoot large
    let ep := coefficient_degree_pos E (bigRoot_n hn)
    let F := Classical.choice (sourcePolynomial_exists _ ep)
    publicSparseRun E reg σ =
      (frozenActiveRoot E reg σ F (publicSparse_log_gate E large) hn ⟨0, ep⟩).map
        (fun r => (rootConstant E F ep r.value, r.localTrace)) := by
  intro hn ep F
  rw [publicSparseRun, dif_pos ep]
  change (runPinnedSparse E reg σ F ⟨0, ep⟩).map
    (fun r => (rootConstant E F ep r.value, r.localTrace)) = _
  rw [runPinnedSparse_active E reg σ F (publicSparse_log_gate E large) hn simple ⟨0, ep⟩]

/-- One size assumption gives the actual sparse route, exact returned
count and the lower bound on root digit steps of its returned trace. -/
theorem publicSparseRun_count_and_work (E : Finset (V × V)) (simple : Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (large : sizeCutoff < n (V := V)) :
    dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse ∧
      ∃ trace, publicSparseRun E reg σ = some (PinnedCNF.modelCount (PinnedCNF.formula E σ), trace) ∧
        (2 : ℝ)^((n (V := V) : ℝ) / (2 * Real.sqrt (Real.logb 2 (n (V := V))))) ≤
          ((Execution.executedDigits trace).length : ℝ) := by
  let hn := sizeCutoff_bigRoot large
  let ep := coefficient_degree_pos E (bigRoot_n hn)
  let F := Classical.choice (sourcePolynomial_exists _ ep)
  have hsize : max (2^131071 : ℕ) 0 < n (V := V) := by
    rw [max_eq_left (Nat.zero_le _)]
    exact hn
  obtain ⟨r, hr, hc, hw⟩ := frozenActiveRoot_count_and_work E reg σ F simple 0
    hsize (publicSparse_log_gate E large) hn ⟨0, ep⟩
  refine ⟨(sparse_entry_admissible E simple reg σ large).1, r.localTrace, ?_, hw⟩
  rw [publicSparseRun_active E simple reg σ large, hr, Option.map_some, hc]

#print axioms publicSparseRun
#print axioms publicSparseRun_count_projection
#print axioms publicSparse_log_gate
#print axioms publicSparseRun_active
#print axioms publicSparseRun_count_and_work

#check @publicSparseRun_count_and_work

end RootSeparation.Preprocessing
