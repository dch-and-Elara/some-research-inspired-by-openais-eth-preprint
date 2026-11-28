import J6R32StatefulArithmeticNative

/-! The reference arithmetic carries no job state. Its raw value is
uniquely determined by the already verified source result. The real
recursive interpreter has a single live bank and its exact fees split
into local native arithmetic, physical complex publication, and the
actual live leaf readers plus per-descent control. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R21Leaf J6R24MeteredRecursion J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => AnyLedger f ell key prec tw bw
local notation "J" => GJob f ell key prec tw bw

variable (T : Prepared cfg sel r hf)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

set_option maxHeartbeats 7800000 in
theorem reference_source (c : Call (PhysicalHost f ell)) (hc : NativeReach (Plan sel) r c) :
    (T.frame hc).decode (reference T c hc).result=(sourceBlueprint sel r hf).program.run c := by
  by_cases stop : c.edges≤(S).cutoff
  · rw [reference_leaf (T:=T) hc stop]
    exact T.correctAt c hc
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel hc T.rootStable a
    let D := T.active c hc a
    rw [reference,dif_neg stop]
    let go : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      reference T ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)
    have sub (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
        (T.bank (registerPrecision S c t) (register_positive d t)).decode (go t z β g).result=
          (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      exact reference_source _ (reach_snoc (Plan sel) hc w)
    obtain ⟨word,_,hOut,hValue⟩ := actual_active_decoded cfg sel r hf hc d T.rootStable D
      (reachable_positive T hc) T.vPositive go sub
    change (T.frame hc).decode (D.eval (reachable_positive T hc) T.vPositive hf go).result=_
    rw [hOut]
    exact hValue
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

variable {T : Prepared cfg sel r hf}
variable (R : Resident T key prec tw bw)

set_option maxHeartbeats 4000000 in
omit [Fact (Irreducible (NativeProbeRing.residuePoly f))] in
theorem live_leaf_source {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(S).cutoff) (B : L) (good : Ancestors R.births R.rootLive p B) :
    (T.frame p.reached).decode ((R.leaf p stop).execute hf (T.frame p.reached) T.vPositive B).result=
      (sourceBlueprint sel r hf).program.run c := by
  let F := T.frame p.reached
  let D := R.leaf p stop
  have entry (x : Fin c.edges→Bool) (v : c.host.Row⊕c.host.Col) :
    J6R18ChildWrite.castBox F.exactMod (uvRead F.hp F.words ell (D.read hf F T.vPositive B v (List.ofFn x)).result)=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘c.host.edgeOrder c.edges D.sameEdges) v) :=
    (boxTransport_cast F.exactMod _).symm.trans (R.sourceLeaf p stop B good x v)
  change F.decode (D.execute hf F T.vPositive B).result=_
  rw [LeafCode.execute,clocked_leaf_is_native_enumerator F.hp F.sizePos T.vPositive D.nodes _ D.clock D.clockShape]
  exact (boxTransport_cast F.exactMod _).trans
    (actual_leaf_is_printed_stop sel r c hf stop F.hp F.sizePos T.vPositive F.exactMod
      D.sameEdges D.nodes D.unique D.complete (D.read hf F T.vPositive B) entry)

set_option maxHeartbeats 10500000 in
theorem native_follows (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    Follows (Ancestors R.births R.rootLive p) (native R c p) (reference T c p.reached) (nativeLog R c p) := by
  by_cases stop : c.edges≤(S).cutoff
  · rw [log_leaf R p stop,reference_leaf (T:=T) p.reached stop]
    intro B _ live
    rw [native_leaf R p stop B]
    have same := (live_leaf_source R p stop B live).trans (T.correctAt c p.reached).symm
    exact ⟨frame_words_injective hf (T.frame p.reached) same,rfl,by simp only [bare,chronologicalBill,Nat.zero_add]⟩
  · let a := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let A := T.active c p.reached a
    let I := Ancestors R.births R.rootLive p
    let ph := reachable_positive T p.reached
    let run : ActiveChildS (sel:=sel) L T.bank d := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      withPublished (R.births p w).job (native R ((Plan sel).child c w) (.step p w))
        (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp)
    let answer : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      reference T ((Plan sel).child c w) (reach_snoc (Plan sel) p.reached w)
    let logs : ActiveLog (sel:=sel) (c:=c) L J := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      Log.enter (R.births p w).job (nativeLog R ((Plan sel).child c w) (.step p w))
    rw [native,dif_neg stop,reference,dif_neg stop,nativeLog,dif_neg stop]
    change Follows I (activeS A ph T.vPositive hf run) (A.eval ph T.vPositive hf answer) (callLog A logs)
    apply active_follows (ancestors_stable R.births R.stableRoot p)
    intro t z β g
    let w := addressed (sel:=sel) d t z β g
    have next : Follows (Ancestors R.births R.rootLive (.step p w))
        (native R ((Plan sel).child c w) (.step p w))
        (reference T ((Plan sel).child c w) (Path.step p w).reached)
        (nativeLog R ((Plan sel).child c w) (.step p w)) :=
      native_follows _ (.step p w)
    exact enter_traced (Q:=Ancestors R.births R.rootLive (.step p w)) (R.births p w).job _ _ _ _ _
      (fun bank good inheritance=>ancestors_enter R.births R.stableRoot p w bank _ good inheritance) next
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

theorem whole_live_subtree (c : Call (PhysicalHost f ell)) (p : Path sel r c) (B : L)
    (legal : JobsReady B (nativeLog R c p).jobs) (live : Ancestors R.births R.rootLive p B) :
    let out := native R c p B
    let log := nativeLog R c p
    (T.frame p.reached).decode out.result.1=(sourceBlueprint sel r hf).program.run c ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(reference T c p.reached).steps+chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨raw,bank,fee⟩ := native_follows R c p B legal live
  exact ⟨(congrArg (T.frame p.reached).decode raw).trans (reference_source T c p.reached),bank,fee⟩

theorem whole_live_root (B : L) (ready : JobsReady B (nativeLog R r .root).jobs) (live : R.rootLive B) :
    let out := native R r .root B
    let log := nativeLog R r .root
    (T.frame (.reflexive r)).decode out.result.1=(sourceBlueprint sel r hf).program.run r ∧
      out.result.2.headers=(log.jobs.map (fun j=>j.entry.result)).reverse++B.headers ∧
      out.result.2.records=(log.jobs.map Job.immutable).reverse++B.records ∧
      out.steps=(reference T r (.reflexive r)).steps+chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨value,state,fee⟩ := whole_live_subtree R r .root B ready live
  have bank := after_jobs_views B (nativeLog R r .root).jobs
  exact ⟨value,(congrArg Ledger.headers state).trans bank.1,(congrArg Ledger.records state).trans bank.2,fee⟩

#print axioms reference_source
#print axioms live_leaf_source
#print axioms native_follows
#print axioms whole_live_subtree
#print axioms whole_live_root
end J6R32StatefulArithmetic
