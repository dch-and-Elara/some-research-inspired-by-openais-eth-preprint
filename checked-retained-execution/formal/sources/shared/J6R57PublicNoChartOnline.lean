import J6R57PublicNoChartLeaf
import J6R34OfficialGatewayCore

namespace J6R57Public
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}

open J6R49Leaf A1R12
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
abbrev OwnerInputProvider :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
    (_ : ((Plan sel).child c w).edges≤((printedParams (f:=f) (ell:=ell) s)).cutoff), Meter (Option (OwnerTerminalInput X p w Y))

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin ((exteriorChild G ell X.centre X.sample X.group)).edges≃((exteriorChild G ell X.centre X.sample X.group)).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)

def HasMeasuredOwnerInputs : Prop :=
  ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges≤((printedParams (f:=f) (ell:=ell) s)).cutoff),
    0<((Plan sel).child c w).edges→
      (ownerInputs p w (sourceState M p w) stop).result.isSome

section Branch
variable {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (stop : ((Plan sel).child c w).edges≤((printedParams (f:=f) (ell:=ell) s)).cutoff)
variable (B : (PageBank f ell key prec tw bw (pageKeyWidth m+pad)))

def finishOwnerAttempt {width : ℕ} (F : Frame f width) (op : Meter (Option (Block F ell))) :
    Meter (Block F ell) :=
  match op.result with
  | some word => ⟨word,op.steps+3⟩
  | none => let z : Meter (Block F ell) := zeroM F.hp
            ⟨z.result,op.steps+z.steps+4⟩

private theorem finish_owner_attempt_success {width : ℕ} (F : Frame f width)
    (op : Meter (Option (Block F ell))) (word : Block F ell)
    (h : op.result=some word) :
    finishOwnerAttempt F op=⟨word,op.steps+3⟩ := by
  cases op with
  | mk value fee =>
    change value=some word at h
    subst value
    rfl
def runOwnerPositive : Meter (Block (T.frame (Path.step p w).reached) ell) :=
  let F := T.frame (Path.step p w).reached
  let input := ownerInputs p w Y stop
  match input.result with
  | none => let z : Meter (Block F ell) := zeroM F.hp
            ⟨z.result,input.steps+z.steps+4⟩
  | some A => finishOwnerAttempt F (executeOwnerTerminal X p w Y ⟨A,input.steps⟩ F B)

theorem accepted_owner_inputs_use_the_actual_reader
    (A : OwnerTerminalInput X p w Y)
    (hit : (ownerInputs p w Y stop).result=some A)
    (word : Block (T.frame (Path.step p w).reached) ell)
    (succeeded : (executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩
      (T.frame (Path.step p w).reached) B).result=some word) :
    runOwnerPositive (X:=X) (ownerInputs:=ownerInputs) (p:=p) (w:=w) (Y:=Y) (stop:=stop) (B:=B)=
      ⟨word,(executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩
        (T.frame (Path.step p w).reached) B).steps+3⟩ := by
  unfold runOwnerPositive
  dsimp only
  rw [hit]
  dsimp only
  exact finish_owner_attempt_success (T.frame (Path.step p w).reached)
    (executeOwnerTerminal X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩
      (T.frame (Path.step p w).reached) B) word succeeded
end Branch

def withPaidOwnerLeaves : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate :=
  {M with
    leafRoot := fun stop=>sourceRootTerminal X pad (machineInputs X pad M) basePos stop ord
    leafAfter := fun {c} p w Y stop B =>
      if ((Plan sel).child c w).edges=0 then
        let old := literalLeafExec X pad (machineInputs X pad M) basePos (Path.step p w) stop
          (actualEdgeOrder T (p.ticket w) Y.birth.native.physical) B
        ⟨old.result,(storedBook Y).steps+old.steps+3⟩
      else runOwnerPositive (X:=X) (ownerInputs:=ownerInputs) (p:=p) (w:=w) (Y:=Y) (stop:=stop) (B:=B)}

theorem paid_owner_leaf_keeps_actual_source :
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (w : (Plan sel).Slot c),
      sourceState (withPaidOwnerLeaves X M basePos ord ownerInputs) p w=sourceState M p w := by
  intro c p
  induction p with
  | root => intro w; rfl
  | step p j ih =>
    intro w
    rw [sourceState,sourceState,ih j]
    all_goals rfl

theorem paid_owner_leaf_keeps_births :
    ((fun {_} p w=>borns (withPaidOwnerLeaves X M basePos ord ownerInputs) p w) :
      Births T key prec tw bw (pageKeyWidth m+pad))=(fun {_} p w=>borns M p w) := by
  funext c p w
  exact congrArg StoredSite.birth (paid_owner_leaf_keeps_actual_source X M basePos ord ownerInputs p w)

variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
variable (initial : (PageBank f ell key prec tw bw (pageKeyWidth m+pad)))

include boot in
theorem same_source_terminal_agrees_without_LoopCharts
    (gateWidth : gate.created.val=base)
    (rootLive : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (borns M) initial)
    (measured : HasMeasuredOwnerInputs X M ownerInputs) :
    LeafAgreement (withPaidOwnerLeaves X M basePos ord ownerInputs) initial := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  refine ⟨?_,?_⟩
  · intro stop
    exact source_root_terminal_unchanged X pad (machineInputs X pad M) basePos stop ord initial rootLive
  · intro c p w stop
    let walk := Path.step p w
    let F := T.frame walk.reached
    let Q := stackBank (borns M) initial walk
    let Y := sourceState M p w
    have bankEq : stackBank (borns R) initial walk=Q :=
      congrArg (fun BB : Births T key prec tw bw (pageKeyWidth m+pad)=>stackBank BB initial walk)
        (paid_owner_leaf_keeps_births X M basePos ord ownerInputs)
    have live : opened (borns M) (IsLive (X.seed pad)) walk Q :=
      stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
        rootLive valid walk
    change F.decode (R.leafAfter p w (sourceState R p w) stop
        (stackBank (borns R) initial walk)).result=_
    rw [bankEq,paid_owner_leaf_keeps_actual_source X M basePos ord ownerInputs p w]
    by_cases zero : ((Plan sel).child c w).edges=0
    · simp only [R,withPaidOwnerLeaves,if_pos zero]
      exact literal_leaf_exec_correct X pad (machineInputs X pad M) basePos walk stop
        (actualEdgeOrder T (p.ticket w) Y.birth.native.physical) Q live
    · simp only [R,withPaidOwnerLeaves,if_neg zero]
      have positive := Nat.pos_of_ne_zero zero
      have prep := measured p w stop positive
      change (ownerInputs p w Y stop).result.isSome at prep
      cases hit : (ownerInputs p w Y stop).result with
      | none => simp [hit] at prep
      | some A =>
        have rootHere := opened_keeps_root X pad (borns M) walk Q live
        obtain ⟨word,read,decode⟩ :=
          actual_owner_terminal_correct_without_legacy_chart X M gate boot p w
            ⟨A,(ownerInputs p w Y stop).steps⟩ F Q gateWidth basePos positive
            (IsLive (X.seed pad)) rootHere live
        rw [accepted_owner_inputs_use_the_actual_reader X ownerInputs p w Y stop Q A hit word read]
        exact decode.trans (true_source_stops_on_same_host T walk stop)

#print axioms HasMeasuredOwnerInputs
#print axioms accepted_owner_inputs_use_the_actual_reader
#print axioms withPaidOwnerLeaves
#print axioms paid_owner_leaf_keeps_actual_source
#print axioms paid_owner_leaf_keeps_births
#print axioms same_source_terminal_agrees_without_LoopCharts
end
end J6R57Public


namespace J6R57Public
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
open J6R48DFS J6R34OfficialGateway
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin ((exteriorChild G ell X.centre X.sample X.group)).edges≃((exteriorChild G ell X.centre X.sample X.group)).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (initial : (PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

/-- The already-live bank is the actual incoming bank; this operation
does not rerun the exterior installer. -/
def paidOwnerRunLive : Meter (Block (T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).reached) ell × (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) :=
  letI := sourceDecision sel (exteriorChild G ell X.centre X.sample X.group)
  runRoot (withPaidOwnerLeaves X M basePos ord ownerInputs) retire initial

include boot in
theorem paid_owner_run_from_existing_live_bank
    (gateWidth : gate.created.val=base) (degree : 0<f.natDegree)
    (rootLive : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (borns M) initial)
    (measured : HasMeasuredOwnerInputs X M ownerInputs) :
    let out := paidOwnerRunLive X M basePos ord ownerInputs initial retire
    ((T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).reached)).decode out.result.1=reduce ((exteriorChild G ell X.centre X.sample X.group)).prec f ell (((exteriorChild G ell X.centre X.sample X.group)).host.contract X.hf) ∧
      out.result.2=initial := by
  letI := sourceDecision sel (exteriorChild G ell X.centre X.sample X.group)
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  have births := paid_owner_leaf_keeps_births X M basePos ord ownerInputs
  have same : ReadyOnStack (borns M) initial=ReadyOnStack (borns R) initial :=
    congrArg (fun H : Births T key prec tw bw (pageKeyWidth m+pad)=>ReadyOnStack H initial) births.symm
  have ready : ReadyOnStack (borns R) initial :=
    @Eq.mp (ReadyOnStack (borns M) initial) (ReadyOnStack (borns R) initial)
      same (fun {_} p w=>valid p w)
  have leaves := same_source_terminal_agrees_without_LoopCharts X M basePos ord ownerInputs
    gate boot initial gateWidth rootLive (fun {_} p w=>valid p w) measured
  have main := full_online_selected_source R initial retire (fun {_} p w=>ready p w) leaves
  let exterior := exteriorChild G ell X.centre X.sample X.group
  exact ⟨main.1.trans (J6R12Integral.printed_run_exact cfg sel exterior T.rootStable X.hf degree),main.2⟩

def paidOwnerReceiptFromLive
    (gateWidth : gate.created.val=base) (degree : 0<f.natDegree)
    (rootLive : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (borns M) initial)
    (measured : HasMeasuredOwnerInputs X M ownerInputs) :
    GroupReceipt (ell:=ell) G X.hf X.centre X.sample X.group where
  frame := (T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).reached)
  run := let step := paidOwnerRunLive X M basePos ord ownerInputs initial retire
         ⟨step.result.1,step.steps⟩
  truth := (paid_owner_run_from_existing_live_bank X M basePos ord ownerInputs initial retire gate boot
    gateWidth degree rootLive (fun {_} p w=>valid p w) measured).1

#print axioms paidOwnerRunLive
#print axioms paid_owner_run_from_existing_live_bank
#print axioms paidOwnerReceiptFromLive
end
end J6R57Public

