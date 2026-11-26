import SolverNativeRun

noncomputable section
namespace RootSeparation.Solver
open Entry S11 SourceDensity GraphCutMoments Execution Classical

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (F : SourcePolynomial (4*lambda (size E)))
variable (hs : 2^40 ≤ lambda (size E)) (hn : bigRoot (n (V := V)))

def frozenRootState (hbig : bigRoot (n (V := V))) : NativeState (s := size E) F := by
  refine ⟨rootCall E reg σ F, ?_, ?_⟩
  · change 1 * Fintype.card (Wire E) ≤ 3*size E
    have hm := wire_count E reg
    have h := (dimensions E reg).2
    omega
  · have h₃ : 3 ≤ degreeEnvelope (size E) := by
      have hm : rootM E = 10*n (V := V) := wire_count E reg
      have h := (dimensions E reg).2
      exact (root_numeric (root_lambda E hbig) (M := rootM E) (by omega) (by omega)).2.2.2.1
    constructor
    · intro x
      refine le_of_eq_of_le ?_ ((row_degree E reg x).trans h₃)
      simp only [fiberCount, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.refl _)
    · intro y
      refine le_of_eq_of_le ?_ (show 2 ≤ degreeEnvelope (size E) by omega)
      refine Eq.trans ?_ (col_degree E y)
      simp only [fiberCount, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.refl _)

def frozenRootGroup (t : RootCenter E) (j : RootProbe E) (β : List ℕ) (g : Fin 64) :
    NativeState (s := size E) F :=
  let G := rootLayout E reg σ F hn
  let h := active_numeric (size E) _ _ hs (frozenRootState E reg σ F hn).load G.positive
  childState F (frozenRootState E reg σ F hn) G (probes_fit E reg hn) h.2.2.2.2.1 t j β g

def frozenRootBatch (track : Fin (4*lambda (size E))) (t : RootCenter E) (j : RootProbe E) :
    Option (BatchState (Fin (4*lambda (size E))) (nativePrecision E t.val)) :=
  checkedBatch (nativePrecision E t.val) (rootCodec E F t.val) track
    (fun slot g => (runNativeCall F hs track (frozenRootGroup E reg σ F hs hn t j slot.exponents g)).map
      CallResult.value)
    (modeWeights ((chosenPacking E reg hn).mixedAt t.val) (level t.val) (nativePrecision E t.val))
    t.val j.val

abbrev RootProbeStates := (t : RootCenter E) → RootProbe E →
    BatchState (Fin (4*lambda (size E))) (nativePrecision E t.val)

def traceFromRoot (state : RootProbeStates E) : List Step :=
  (centers (rootU E) (rootL E)).toList.attach.flatMap fun pos =>
    let t : RootCenter E := ⟨pos.val, Finset.mem_toList.1 pos.property⟩
    (List.finRange (probeCount (rootM E) (rootL E))).flatMap fun j => (state t j).trace

theorem traceFromRoot_project (state : RootProbeStates E)
    (h : ∀ t j, rootProjection (state t j).trace =
      batch ((chosenPacking E reg hn).mixedAt t.val) t.val j.val (nativePrecision E t.val)) :
    rootProjection (traceFromRoot E state) =
      rootSlots (rootU E) (rootM E) (rootL E) (rootA E) (initialPrecision (V := V))
        (chosenPacking E reg hn).mixedAt := by
  unfold traceFromRoot rootSlots
  have proj {α : Type} (l : List α) (f : α → List Step) :
      rootProjection (l.flatMap f) = l.flatMap (fun a => rootProjection (f a)) := by
    simp only [rootProjection,executedDigits,List.filterMap_flatMap]
  simp only [proj,h]
  conv_rhs =>
    rw [← List.attach_map_subtype_val (centers (rootU E) (rootL E)).toList, List.flatMap_map]
  apply congrArg (fun f => List.flatMap f _)
  funext pos
  conv_rhs =>
    rw [← List.map_coe_finRange (probeCount (rootM E) (rootL E)), List.flatMap_map]

/-- The frozen sparse root uses exactly the selected uncloned root
    packing. Numeric and trace outputs are projections of the same
    checked batches, with actual recursive child evaluation. -/
def frozenActiveRoot (track : Fin (4*lambda (size E))) :
    Option (CallResult F.f (initialPrecision (V := V))) := do
  if h : ∀ t j, (frozenRootBatch E reg σ F hs hn track t j).isSome then
    let state (t : RootCenter E) (j : RootProbe E) :=
      (frozenRootBatch E reg σ F hs hn track t j).get (h t j)
    let samples : RootSamples E F := fun t j => (rootCodec E F t.val).symm (state t j).accumulator
    let trace := traceFromRoot E state
    let value ← tryRootWord E reg F hn samples
    pure ⟨value,trace⟩
  else none

theorem frozenActiveRoot_project (track : Fin (4*lambda (size E)))
    (r : CallResult F.f (initialPrecision (V := V)))
    (hr : frozenActiveRoot E reg σ F hs hn track = some r) :
    rootProjection r.localTrace =
      rootSlots (rootU E) (rootM E) (rootL E) (rootA E) (initialPrecision (V := V))
        (chosenPacking E reg hn).mixedAt := by
  unfold frozenActiveRoot at hr
  split at hr
  · rename_i hall
    let state (t : RootCenter E) (j : RootProbe E) :=
      (frozenRootBatch E reg σ F hs hn track t j).get (hall t j)
    let samples : RootSamples E F := fun t j => (rootCodec E F t.val).symm (state t j).accumulator
    change (tryRootWord E reg F hn samples).bind (fun v => some ⟨v,traceFromRoot E state⟩) =
      some r at hr
    cases h : tryRootWord E reg F hn samples with
    | none => simp [h] at hr
    | some v =>
      rw [h,Option.bind_some,Option.some.injEq] at hr
      rw [← hr]
      apply traceFromRoot_project E reg hn
      intro t j
      have hb : frozenRootBatch E reg σ F hs hn track t j = some (state t j) :=
        (Option.some_get (hall t j)).symm
      exact checkedBatch_project _ (nativePrecision_positive E t.val) _ _ _ _ _ _ _ hb
  · cases hr

theorem frozenActiveRoot_lower (track : Fin (4*lambda (size E)))
    (r : CallResult F.f (initialPrecision (V := V)))
    (hr : frozenActiveRoot E reg σ F hs hn track = some r)
    (simple : Simple E) (cutoff : ℕ) (large : max (2^131071) cutoff < n (V := V)) :
    (2:ℝ)^((n (V := V):ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      ((executedDigits r.localTrace).length : ℝ) := by
  let reference : NativeChild E ℤ := fun _ _ _ _ => 0
  have hK : cutoff < size E := ((le_max_right _ _).trans_lt large).trans_le (by unfold size; omega)
  have h := FourthPaperReview.exponential_root_visits E reg simple σ cutoff reference large
  rw [runEvents_active E simple reg σ cutoff reference hn hK,sourceTrace_eq_slots,
    ← frozenActiveRoot_project E reg σ F hs hn track r hr] at h
  exact h.trans (by
    exact_mod_cast (List.length_filterMap_le (f := Digit.firstSlot) (l := executedDigits r.localTrace)))

section SparseEntry

/-- Entry for the fourth paper's sparse branch. The finite exceptional
    range uses the direct network leaf selected by Appendix D. -/
def runPinnedSparse (track : Fin (4*lambda (size E))) :
    Option (CallResult F.f (initialPrecision (V := V))) :=
  if dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse then
    if hl : 2^40 ≤ lambda (size E) then
      if hN : bigRoot (n (V := V)) then
        frozenActiveRoot E reg σ F hl hN track
      else some ⟨leafValue (rootCall E reg σ F), []⟩
    else some ⟨leafValue (rootCall E reg σ F), []⟩
  else none

def decodePinned (track : Fin (4*lambda (size E))) : Option ℕ :=
  (runPinnedSparse E reg σ F track).map
    (fun result => rootConstant E F (Nat.zero_lt_of_lt track.isLt) result.value)

theorem runPinnedSparse_active (simple : Simple E) (track : Fin (4*lambda (size E))) :
    runPinnedSparse E reg σ F track = frozenActiveRoot E reg σ F hs hn track := by
  rw [runPinnedSparse, simpleNormalize_pinned E simple σ,
    if_pos (dispatch_pinned E reg σ (bigRoot_n hn)), dif_pos hs, dif_pos hn]

theorem decodePinned_finite (track : Fin (4*lambda (size E)))
    (hdispatch : dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse)
    (hsmall : lambda (size E) < 2^40) :
    decodePinned E reg σ F track = some (PinnedCNF.modelCount (PinnedCNF.formula E σ)) := by
  rw [decodePinned,runPinnedSparse,if_pos hdispatch,dif_neg (not_le_of_gt hsmall)]
  exact congrArg some (rootLeaf_count E reg σ F _)

end SparseEntry

end RootSeparation.Solver

#print axioms RootSeparation.Solver.frozenRootState
#print axioms RootSeparation.Solver.frozenRootGroup
#print axioms RootSeparation.Solver.frozenRootBatch
#print axioms RootSeparation.Solver.frozenActiveRoot
#print axioms RootSeparation.Solver.frozenActiveRoot_project
#print axioms RootSeparation.Solver.frozenActiveRoot_lower
#print axioms RootSeparation.Solver.runPinnedSparse_active
#print axioms RootSeparation.Solver.decodePinned_finite
