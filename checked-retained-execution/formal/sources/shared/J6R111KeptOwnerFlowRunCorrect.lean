import J6R111KeptOwnerFlowRun
import J6R51OnlineCorrect

/-! Prove correctness of the retained recursion with its own billed
callbacks. Only the original zero branch is reused as a stop assumption;
the positive read is proved directly on the real entered bank. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R35RootOrigins J6R53TerminalExterior J6R54ExteriorOwner J6R52Terminal J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 34000000
set_option maxRecDepth 5700
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def ZeroSourceAgreement : Prop :=
  ∀ {c : Call (PhysicalHost f ell)} (path : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
    (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff),
    ((Plan sel).child c w).edges=0→
    (T.frame (Path.step path w).reached).decode
      (M.leafAfter path w (sourceState M path w) stop (stackBank (borns M) initial (.step path w))).result=
      (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run ((Plan sel).child c w)

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (basePos : 0<base)
variable (valid : ReadyOnStack (borns M) initial) (live : IsLive (X.seed pad) initial)
variable (zeros : ZeroSourceAgreement X M initial)

include boot gateWidth basePos valid live zeros in
theorem run_retained_decodes_the_same_printed_physical_host
    (x : KeptInvocation X M)
    (bank : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot)) :
    (T.frame (Path.step x.path x.slot).reached).decode (runRetained X M D retire x).result.1=
      (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run x.call := by
  let motive (y : KeptInvocation X M) : Prop :=
    y.entry.bank=stackBank (borns M) initial (.step y.path y.slot) →
      (T.frame (Path.step y.path y.slot).reached).decode (runRetained X M D retire y).result.1=
        (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run y.call
  have all (y : KeptInvocation X M) : motive y := by
    refine (measure (fun z : KeptInvocation X M=>z.call.edges)).wf.induction (C:=motive) y ?_
    intro cur ih atLive
    let current := cur.call
    let path := Path.step cur.path cur.slot
    let sp := printedParams (f:=f) (ell:=ell) s
    let B := cur.entry.bank
    by_cases stop : current.edges≤sp.cutoff
    · by_cases zero : current.edges=0
      · have s : cur.call.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff := stop
        have z : cur.call.edges=0 := zero
        rw [run_retained_unfolds_to_the_actual_child_callback]
        simp only [retainedBody,dif_pos s,if_pos z]
        rw [atLive,cur.actualSite]
        exact zeros cur.path cur.slot s z
      · have positive : 0<cur.call.edges := Nat.pos_of_ne_zero zero
        rw [retained_runner_uses_the_live_positive_leaf_without_a_provider X M D retire cur stop positive]
        have stack : opened (borns M) (IsLive (X.seed pad)) path B := by
          change cur.entry.bank=stackBank (borns M) initial path at atLive
          rw [show B=stackBank (borns M) initial path from atLive]
          exact stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad)) live valid path
        have rootHere := opened_keeps_root X pad (borns M) path B stack
        have proof := positive_continuation_reads_the_exact_live_bank_and_decodes_the_true_leaf
          X cur.path cur.slot cur.site cur.entry M gate boot cur.actualSite gateWidth basePos positive rootHere stack
        exact proof.1.trans (true_source_stops_on_same_host T path stop)
    · let on := Nat.lt_of_not_ge stop
      let d := readyAtPath T path on
      let heads := readGroupHeadersForActive X cur.path cur.slot cur.site cur.entry
      let W := D.layout cur on heads.result
      let layout := selectedLayoutAndLabels W.setup
      let A := prepareFromKeptLayout X cur.path cur.slot cur.site cur.entry M on layout.result
        (D.fit path on) D.masks layout.steps
      let mounted := mountResident cur.site cur.entry.resident
      let scope (u : (Plan sel).Slot current) :=
        retainActualSelectedDemand X cur.path cur.slot cur.site cur.entry M u heads.result
      let ownsKeys (u : (Plan sel).Slot current) := actual_live_keys_at_the_selected_site X M D cur u
      let names (u : (Plan sel).Slot current) :=
        checkedChildLabelWords X cur.path cur.slot cur.site cur.entry M on heads.result W u mounted.result
          (ownsKeys u) layout.result rfl
      let sibling (u : (Plan sel).Slot current) :=
        selected_load_emits_the_actual_driver_source_after_retention X cur.path cur.slot cur.site
          cur.entry M u heads.result mounted.result cur.actualSite
      let childCall (u : (Plan sel).Slot current)
          (entry : CapturedEntry X path u
            (produceCacheSidecarOnce (scope u).result.load mounted.result).result.next) : InvocationOut X M
            ⟨current,path,u,_,sibling u,entry⟩ :=
        runRetained X M D retire ⟨current,path,u,_,sibling u,entry⟩
      let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
        let u := addressed (sel:=sel) d t z β g
        project (nextR66OwnerScope X cur.path cur.slot cur.site u (scope u) mounted.result (ownsKeys u) retire
          (names u) (childCall u)
          (zeroM (T.bank (registerPrecision sp current t) (register_positive d t)).hp) B)
      have trueChild (t : Center sp current) (z : Probe sp current)
          (β : NativeMenu (N sel) current t) (g : Fin 64) :
          (T.bank (registerPrecision sp current t) (register_positive d t)).decode (read t z β g).result=
          (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run
            ((Plan sel).child current ⟨⟨t,z,β,g⟩,d.active⟩) := by
        let u := addressed (sel:=sel) d t z β g
        let next := (produceCacheSidecarOnce (scope u).result.load mounted.result).result.next
        let low := T.bank (registerPrecision sp current t) (register_positive d t)
        have legal : JobsReady B [next.birth.job] := by
          rw [show next=sourceState M path u from sibling u,show B=stackBank (borns M) initial path from atLive]
          exact valid path u
        have op := next_R66_scope_keeps_the_paid_roster_and_actual_installed_resident
          X cur.path cur.slot cur.site u (scope u) mounted.result (ownsKeys u) retire
            (names u) (childCall u) (zeroM low.hp : Meter (Block low ell)) B legal
        let entered : CapturedEntry X path u next :=
          ⟨(installResidentBank next).result,afterOne B next.birth.job,rfl,
            carriedRosterAtEmission X cur.path cur.slot cur.site u (scope u) mounted.result (ownsKeys u),names u⟩
        let arg : KeptInvocation X M := ⟨current,path,u,next,sibling u,entered⟩
        have bank : entered.bank=stackBank (borns M) initial (.step path u) := by
          change afterOne B next.birth.job=_
          rw [show next=sourceState M path u from sibling u,show B=stackBank (borns M) initial path from atLive]
          rfl
        change low.decode (project (nextR66OwnerScope X cur.path cur.slot cur.site u (scope u) mounted.result
          (ownsKeys u) retire (names u) (childCall u) (zeroM low.hp : Meter (Block low ell)) B)).result=_
        rw [op]
        exact ih arg ((Plan sel).smaller current u) bank
      let hp := reachable_positive T path.reached
      obtain ⟨_,_,correct,truth⟩ := actual_active_decoded cfg sel (exteriorChild G ell X.centre X.sample X.group)
        X.hf path.reached d T.rootStable A.result.proofView.prior hp T.vPositive read trueChild
      rw [run_retained_unfolds_to_the_actual_child_callback]
      have stopped : ¬cur.call.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff := stop
      simp only [retainedBody,dif_neg stopped]
      change (T.bank current.prec hp).decode (A.result.eval M.modeWidth hp T.vPositive X.hf read).result=_
      rw [A.result.exact_sweep_matches_its_own_proof_view,active_stream_value A.result.proofView M.modeWidth hp T.vPositive X.hf read,correct]
      exact truth
  exact all x bank

#print axioms run_retained_decodes_the_same_printed_physical_host
end
end J6R111KeptOwnerFlow

