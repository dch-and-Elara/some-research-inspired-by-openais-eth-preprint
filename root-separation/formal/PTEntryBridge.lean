import PTPreprocess
import PTAdmissibility
import RootProgram
import CutoffExample
import SolverPolynomialChoice

namespace RootSeparation.Preprocessing

open Entry S11 GraphCutMoments
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

def sizeCutoff : ℕ := 2^(depthLogCutoff-1)

lemma n_le_size (E : Finset (V × V)) : n (V := V) ≤ size E := by
  unfold size
  omega

theorem eventual_log (E : Finset (V × V)) (hN : sizeCutoff < n (V := V)) :
    depthLogCutoff ≤ lambda (size E) := by
  have hl : depthLogCutoff-1 < lambda (size E) :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
      (hN.trans_le (n_le_size E))
  omega

lemma sizeCutoff_bigRoot (hN : sizeCutoff < n (V := V)) : bigRoot (n (V := V)) := by
  unfold bigRoot sizeCutoff at *
  exact (Nat.pow_le_pow_right (by decide) (by have := depthLogCutoff_large; omega)).trans_lt hN

/-- A positive cubic input is in the density branch exactly above 16.
The source's bounded direct-enumeration exceptions are a separate issue. -/
theorem sparse_iff (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (hN : 0 < n (V := V)) : useSparse (n (V := V)) (m E) ↔ 16 < n (V := V) := by
  refine ⟨?_,sparse_dispatch E reg⟩
  intro hs
  by_contra! h
  have h1 : Nat.clog 2 (n (V := V)) ≤ 4 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h
  have h2 : Nat.clog 2 (Nat.clog 2 (n (V := V))) ≤ 2 :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr h1
  have hm := hs.trans (Nat.mul_le_mul_left _ h2)
  have hd := (dimensions E reg).1
  omega

/-- Any sequence of edge counts satisfying the local Appendix D child bound.
This overapproximates all choices of packets, probes, and precision modes. -/
inductive ReachSize (M0 : ℕ) : ℕ → ℕ → Prop
  | root : ReachSize M0 0 M0
  | child {d M M' : ℕ} : ReachSize M0 d M → 64*M' ≤ 6*M → ReachSize M0 (d+1) M'

theorem reach_shrink {s M0 d M : ℕ} (h0 : M0 ≤ 3*s) (h : ReachSize M0 d M) :
    M*8^d ≤ 3*s := by
  induction h with
  | root => simpa using h0
  | @child d M M' _ hchild ih =>
    have hm : 8*M' ≤ M := by omega
    rw [show M'*8^(d+1) = (8*M') * 8^d by rw [pow_succ]; ring]
    exact (Nat.mul_le_mul_right _ hm).trans ih

/-- Clean root guard for the actual direct sparse Entry and numerical
admission at every active descendant allowed by Appendix D's shrink rule. -/
theorem sparse_entry_admissible (E : Finset (V × V)) (simple : Entry.Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (hN : sizeCutoff < n (V := V)) :
    dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse ∧
    rootM E = 10*n (V := V) ∧ 2*size E = 7*n (V := V) ∧
    0 < initialPrecision (V := V) ∧ order = 1 ∧
    leafThreshold (size E) < rootM E ∧
    ActiveNumbers (size E) 0 (rootM E) ∧
    Nonempty (Solver.SourcePolynomial (4*lambda (size E))) ∧
    (∀ d M, ReachSize (rootM E) d M → leafThreshold (size E) < M →
      ActiveNumbers (size E) d M) := by
  have hbig := sizeCutoff_bigRoot hN
  have hn := bigRoot_n hbig
  have hLog := eventual_log E hN
  have hM : rootM E = 10*n (V := V) := wire_count E reg
  have hs := (dimensions E reg).2
  have h0 : rootM E ≤ 3 * size E := by omega
  have ha := root_active E reg (by omega)
  have hl : 0 < lambda (size E) := (by decide : 0 < 131072).trans_le (depthLogCutoff_large.trans hLog)
  rw [simpleNormalize_pinned E simple σ]
  exact ⟨dispatch_pinned E reg σ hn,hM,hs,by simp [initialPrecision],rfl,ha,
    active_numbers hLog ha (reach_shrink h0 ReachSize.root),
    Solver.sourcePolynomial_exists _ (by omega),
    fun _ _ hr hActive => active_numbers hLog hActive (reach_shrink h0 hr)⟩

theorem sparse_trace_eventual (E : Finset (V × V)) (simple : Entry.Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    {O : Type*} [CommRing O] (child : NativeChild E O)
    (hN : max sizeCutoff K < n (V := V)) :
    ∃ hn : bigRoot (n (V := V)),
      runEvents E reg σ K child =
        sourceTrace (chosenPacking E reg hn).mixedAt (rootM E) (rootL E) (rootA E)
          (rootU E) (initialPrecision (V := V)) child := by
  have hK : K < size E := ((le_max_right sizeCutoff K).trans_lt hN).trans_le (n_le_size E)
  have hn := sizeCutoff_bigRoot ((le_max_left sizeCutoff K).trans_lt hN)
  exact ⟨hn,runEvents_active E simple reg σ K child hn hK⟩

/-- This counterexample concerns changing the prepass and then applying the
same source wire construction, even though the actual main route uses hashes. -/
theorem all_positive_wire_counterexample (E : Finset (V × V))
    (reg : ∀ v, degree E v = 3) (hN : 0 < n (V := V)) :
    rootM E = 10*n (V := V) ∧
    builtM (Entry.survivingEdges E (fun _ => true)) = 2*n (V := V) ∧
    builtM (Entry.survivingEdges E (fun _ => true)) < rootM E := by
  have h1 : rootM E = 10*n (V := V) := wire_count E reg
  have h2 : builtM (Entry.survivingEdges E (fun _ => true)) = 2*n (V := V) := built_allPositive E
  exact ⟨h1,h2,by omega⟩

/-- The smaller root gate and the original root packing tests can pass while
the asymptotic 4/5-power estimate fails, on an actual simple cubic input. -/
theorem cutoff_graph_example :
    let k := (2:ℕ)^131070
    let E := cliques k
    n (V := Fin k × Fin 4) = 2^131072 ∧
    bigRoot (n (V := Fin k × Fin 4)) ∧
    useSparse (n (V := Fin k × Fin 4)) (m E) ∧
    leafThreshold (size E) < rootM E ∧
    (∃ G : Packing (Wire E) (RootPackets E (cliques_cubic k)) (rootA E) (rootL E),
      G.cell = rootCell E (cliques_cubic k)) ∧
    lambda (size E) = 131074 ∧ retained (size E) 0 = 1 ∧
    retained (size E) 0 ^ 5 < lambda (size E)^4 := by
  intro k E
  have hN : n (V := Fin k × Fin 4) = 2^131072 := by
    change Fintype.card (Fin k × Fin 4) = _
    rw [cliques_size]
    change 4 * (2:ℕ)^131070 = _
    rw [show (4:ℕ)=2^2 by decide, ← pow_add]
  have hbig : bigRoot (n (V := Fin k × Fin 4)) := by
    unfold bigRoot
    rw [hN]
    exact Nat.pow_lt_pow_right (by decide) (by decide)
  have hN' := bigRoot_n hbig
  have hs : size E = 7*2^131071 := by
    have h := (dimensions E (cliques_cubic k)).2
    rw [hN, show (131072:ℕ)=131071+1 by decide, pow_succ] at h
    omega
  obtain ⟨_,G,hG,_,_,_⟩ := root_certified E (cliques_cubic k) hbig
  refine ⟨hN,hbig,sparse_dispatch E (cliques_cubic k) (by omega),root_active E (cliques_cubic k) (by omega),
    ⟨G,hG⟩,?_⟩
  rw [hs]
  exact FourthPaperReview.source_parameter_example

#print axioms sparse_iff
#print axioms reach_shrink
#print axioms sparse_entry_admissible
#print axioms sparse_trace_eventual
#print axioms all_positive_wire_counterexample
#print axioms cutoff_graph_example

end RootSeparation.Preprocessing
