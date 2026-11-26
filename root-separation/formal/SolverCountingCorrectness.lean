import SolverParentCompatibility
import SolverRootRun

noncomputable section
namespace RootSeparation.Solver
open S11 Execution Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))

/-- Mathematical value of each native batch with each child replaced
    by its contraction specification. This batch appears only in the
    inductive proof, never in the execution of an active child. -/
def specBatch (track : Fin (4*lambda s)) (t : callCenters s c) (j : callProbes s c) :
    BatchState (Fin (4*lambda s)) (callPrecision s c t.val) :=
  let p := callPrecision s c t.val
  let codec := wordCoords F.monic F.degree p (callPrecision_pos s c t.val)
  executeBatch p codec track (fun slot g =>
    leafValue (childCall F.monic F.degree G (nativeTables F G cap) t j slot.exponents g))
    (G.weights t.val) t.val j.val

private theorem executeBatch_with_group_contractions {R I B : Type*} [CommSemiring R] [DecidableEq I]
    [Fintype B] (A : AffinePacket (Fin 64) R)
    [∀ g, Fintype (A.Bits g)] [∀ g, Fintype (A.Rows g)] [∀ g, Fintype (A.TargetMode g)]
    (t : ℤ) (j p : ℕ) (e : A.Z ≃ Mode B (level t) p)
    (hw : ∀ z, A.weight z = (e z).2.2.val+1) (hp : (2:R)^p = 0)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → R)
    (hchild : ∀ slot g, child slot g =
      A.child (readExponent (nativeModeOrder A (level t) p e) slot.exponents) g) :
    codec.symm (executeBatch p codec track child (modeWeights B (level t) p) t j).accumulator =
      A.sample := by
  rw [show child = _ by funext slot g; exact hchild slot g]
  exact executeBatch_affine_value A t j p e hw hp codec track

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 1024 in
theorem exactCallProbe_specBatch (track : Fin (4*lambda s)) (t : callCenters s c) (j : callProbes s c) :
    tryWord F.monic (callPrecision s c t.val) (exactCallProbe F G cap t j) =
      some ((wordCoords F.monic F.degree (callPrecision s c t.val) (callPrecision_pos s c t.val)).symm
        (specBatch F G cap track t j).accumulator) := by
  rw [exactCallProbe_affine_sample]
  apply congrArg some
  symm
  unfold specBatch
  let p := callPrecision s c t.val
  let A := (nativeAffineData F G cap t j).affine
  let codec := wordCoords F.monic F.degree p (callPrecision_pos s c t.val)
  apply executeBatch_with_group_contractions A t.val j.val p (unpackActualMode F G t)
    (nativeAffine_weights F G cap t j) (word_two_pow F.f p) codec track
  intro slot g
  let zs := nativeModeOrder A (level t.val) p (unpackActualMode F G t)
  have hval (d : DecidableEq A.Z) :
      leafValue (childCall F.monic F.degree G (nativeTables F G cap) t j slot.exponents g) =
        A.child (@readExponent _ d zs slot.exponents) g := by
    have he : packetExponent F G cap t j slot.exponents = @readExponent _ d zs slot.exponents := by
      rw [packetExponent_native F G cap t j]
      exact congrArg (fun d => @readExponent _ d zs slot.exponents) (Subsingleton.elim _ _)
    exact (affineChild_physical F G cap t j slot.exponents g).symm.trans
      (congrArg (fun β => A.child β g) he)
  exact hval _

set_option maxHeartbeats 2500000 in
/-- Every reached call returns its own contraction modulo its own
    precision. The induction ranges over the actual wire count. -/
theorem runNativeCall_correct (hs : 2^40 ≤ lambda s) (track : Fin (4*lambda s))
    (state : NativeState (s := s) F) :
    ∃ r, runNativeCall F hs track state = some r ∧ r.value = leafValue state.call := by
  induction hn : state.call.edges using Nat.strong_induction_on generalizing state with
  | h n ih =>
    by_cases hactive : leafThreshold s < state.call.edges
    · let c := state.call
      let data := active_numeric s c.depth c.edges hs state.load hactive
      let G := selectCallLayout s c hactive state.degrees data.2.2.1 data.2.2.2.1
      let cap := data.2.2.2.2.2
      let hpack := data.2.2.2.2.1
      let ep (t : callCenters s c) (j : callProbes s c) :=
        let p := callPrecision s c t.val
        checkedBatch p (wordCoords F.monic F.degree p (callPrecision_pos s c t.val)) track
          (fun slot g =>
            (runNativeCall F hs track (childState F state G cap hpack t j slot.exponents g)).map
              CallResult.value)
          (G.weights t.val) t.val j.val
      have hbatch (t : callCenters s c) (j : callProbes s c) :
          ep t j = some (specBatch F G cap track t j) := by
        unfold ep specBatch
        apply checkedBatch_success
        intro β _ g
        let sub := childState F state G cap hpack t j β g
        have hsub : sub.call.edges < n := hn ▸ childCall_shrink F.monic F.degree G
          (nativeTables F G cap) t j β g
        obtain ⟨r,hr,he⟩ := ih sub.call.edges hsub sub rfl
        change (runNativeCall F hs track sub).map CallResult.value = some _
        rw [hr,Option.map_some,he]
        rfl
      have hall : ∀ t j, (ep t j).isSome := by
        intro t j; rw [hbatch]; rfl
      let states : ProbeStates (4*lambda s) s c := fun t j => (ep t j).get (hall t j)
      let decode : CallReturned F c := fun t j =>
        (wordCoords F.monic F.degree (callPrecision s c t.val) (callPrecision_pos s c t.val)).symm
          (states t j).accumulator
      have hsample (t : callCenters s c) (j : callProbes s c) :
          tryWord F.monic (callPrecision s c t.val) (exactCallProbe F G cap t j) =
            some (decode t j) := by
        have hst : states t j = specBatch F G cap track t j :=
          Option.get_of_eq_some (hall t j) (hbatch t j)
        unfold decode
        rw [hst]
        exact exactCallProbe_specBatch F G cap track t j
      have hr := recoverCall_of_probe_residues F G cap data.1 data.2.1 decode hsample
      let trace := (callCenters s c).attach.toList.flatMap fun t =>
        (List.finRange (probeCount c.edges (callL s c))).flatMap fun j => (states t j).trace
      refine ⟨⟨leafValue c,trace⟩,?_,rfl⟩
      rw [runNativeCall,dif_pos hactive]
      change (if he : ∀ t j, (ep t j).isSome then _ else none) = _
      rw [dif_pos hall]
      change (recoverCall F c cap decode).map (fun value =>
        (⟨value,trace⟩ : CallResult F.f c.precision)) = _
      rw [hr,Option.map_some,leafValue_contract]
    · refine ⟨⟨leafValue state.call,[]⟩,?_,rfl⟩
      rw [runNativeCall,dif_neg hactive]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.exactCallProbe_specBatch
#print axioms RootSeparation.Solver.runNativeCall_correct
