import SolverCountingCorrectness

noncomputable section
namespace RootSeparation.Solver
open Entry S11 Execution GraphCutMoments Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (F : SourcePolynomial (4*lambda (size E)))

set_option maxHeartbeats 1300000 in
theorem frozenRootBatch_correct (hs : 2^40 ≤ lambda (size E)) (hn : bigRoot (n (V := V)))
    (track : Fin (4*lambda (size E))) (t : RootCenter E) (j : RootProbe E) :
    frozenRootBatch E reg σ F hs hn track t j =
      some (specBatch F (rootLayout E reg σ F hn) (probes_fit E reg hn) track t j) := by
  unfold frozenRootBatch specBatch
  apply checkedBatch_success
  intro β _ g
  let state := frozenRootGroup E reg σ F hs hn t j β g
  obtain ⟨r,hr,he⟩ := runNativeCall_correct F hs track state
  change (runNativeCall F hs track state).map CallResult.value = _
  rw [hr,Option.map_some,he]
  rfl

theorem root_recoverCall (hn : bigRoot (n (V := V))) (samples : RootSamples E F) :
    tryRootWord E reg F hn samples =
      recoverCall F (rootCall E reg σ F) (probes_fit E reg hn) samples := by
  rfl

set_option maxHeartbeats 2500000 in
theorem frozenActiveRoot_correct (hs : 2^40 ≤ lambda (size E)) (hn : bigRoot (n (V := V)))
    (track : Fin (4*lambda (size E))) :
    ∃ r, frozenActiveRoot E reg σ F hs hn track = some r ∧
      rootConstant E F (Nat.zero_lt_of_lt track.isLt) r.value =
        PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  let G := rootLayout E reg σ F hn
  let cap := probes_fit E reg hn
  let c := rootCall E reg σ F
  have hbatch := frozenRootBatch_correct E reg σ F hs hn track
  have hall : ∀ t j, (frozenRootBatch E reg σ F hs hn track t j).isSome := by
    intro t j
    rw [hbatch]
    rfl
  let state (t : RootCenter E) (j : RootProbe E) :=
    (frozenRootBatch E reg σ F hs hn track t j).get (hall t j)
  let samples : RootSamples E F := fun t j => (rootCodec E F t.val).symm (state t j).accumulator
  have hsample (t : RootCenter E) (j : RootProbe E) :
      tryWord F.monic (nativePrecision E t.val) (exactCallProbe F G cap t j) =
        some (samples t j) := by
    have hst : state t j = specBatch F G cap track t j :=
      Option.get_of_eq_some (hall t j) (hbatch t j)
    unfold samples
    rw [hst]
    exact exactCallProbe_specBatch F G cap track t j
  have hN : rootM E = 10*n (V := V) := wire_count E reg
  have hS := (dimensions E reg).2
  have hnumeric := root_numeric (root_lambda E hn) (M := rootM E) (by omega) (by omega)
  have hr := recoverCall_of_probe_residues F G cap hnumeric.1 hnumeric.2.1 samples hsample
  rw [← root_recoverCall E reg σ F hn] at hr
  refine ⟨⟨leafValue c, traceFromRoot E state⟩,?_,rootLeaf_count E reg σ F _⟩
  unfold frozenActiveRoot
  rw [dif_pos hall]
  change (tryRootWord E reg F hn samples).bind (fun value =>
    some (⟨value,traceFromRoot E state⟩ : CallResult F.f (initialPrecision (V := V)))) = _
  rw [hr,Option.bind_some,leafValue_contract]

theorem decodePinned_count (track : Fin (4*lambda (size E)))
    (hdispatch : dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse) :
    decodePinned E reg σ F track = some (PinnedCNF.modelCount (PinnedCNF.formula E σ)) := by
  by_cases hs : 2^40 ≤ lambda (size E)
  · by_cases hn : bigRoot (n (V := V))
    · obtain ⟨r,hr,hvalue⟩ := frozenActiveRoot_correct E reg σ F hs hn track
      rw [decodePinned,runPinnedSparse,if_pos hdispatch,dif_pos hs,dif_pos hn,hr,Option.map_some,hvalue]
    · rw [decodePinned,runPinnedSparse,if_pos hdispatch,dif_pos hs,dif_neg hn]
      exact congrArg some (rootLeaf_count E reg σ F _)
  · exact decodePinned_finite E reg σ F track hdispatch (Nat.lt_of_not_ge hs)

theorem decodePinned_simple_cubic (simple : Simple E) (hn : 20 ≤ n (V := V))
    (track : Fin (4*lambda (size E))) :
    decodePinned E reg σ F track = some (PinnedCNF.modelCount (PinnedCNF.formula E σ)) := by
  apply decodePinned_count
  rw [simpleNormalize_pinned E simple σ, dispatch_pinned E reg σ hn]

omit F reg σ [DecidableEq V] in
theorem coefficient_degree_pos (hn : 20 ≤ n (V := V)) : 0 < 4*lambda (size E) := by
  apply Nat.mul_pos (by decide)
  apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2
  change 1 < size E
  unfold size m
  omega

/-- Public counting interface, choosing a permitted binary polynomial
    and tracking the constant coefficient. -/
def solveUnclonedPinned (hn : 20 ≤ n (V := V)) : Option ℕ :=
  let h := coefficient_degree_pos E hn
  let f := Classical.choice (sourcePolynomial_exists (4*lambda (size E)) h)
  decodePinned E reg σ f ⟨0,h⟩

omit F in
theorem solveUnclonedPinned_correct (simple : Simple E) (hn : 20 ≤ n (V := V)) :
    solveUnclonedPinned E reg σ hn = some (PinnedCNF.modelCount (PinnedCNF.formula E σ)) :=
  decodePinned_simple_cubic E reg σ _ simple hn _

/-- Correct return and root work on the very same frozen execution. -/
theorem frozenActiveRoot_count_and_work (simple : Simple E) (cutoff : ℕ)
    (large : max (2^131071) cutoff < n (V := V))
    (hs : 2^40 ≤ lambda (size E)) (hn : bigRoot (n (V := V)))
    (track : Fin (4*lambda (size E))) :
    ∃ r, frozenActiveRoot E reg σ F hs hn track = some r ∧
      rootConstant E F (Nat.zero_lt_of_lt track.isLt) r.value =
        PinnedCNF.modelCount (PinnedCNF.formula E σ) ∧
      (2:ℝ)^((n (V := V):ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V))))) ≤
        ((executedDigits r.localTrace).length : ℝ) := by
  obtain ⟨r,hr,hval⟩ := frozenActiveRoot_correct E reg σ F hs hn track
  exact ⟨r,hr,hval,frozenActiveRoot_lower E reg σ F hs hn track r hr simple cutoff large⟩

end RootSeparation.Solver

#print axioms RootSeparation.Solver.frozenRootBatch_correct
#print axioms RootSeparation.Solver.frozenActiveRoot_correct
#print axioms RootSeparation.Solver.decodePinned_simple_cubic
#print axioms RootSeparation.Solver.solveUnclonedPinned_correct
#print axioms RootSeparation.Solver.frozenActiveRoot_count_and_work
