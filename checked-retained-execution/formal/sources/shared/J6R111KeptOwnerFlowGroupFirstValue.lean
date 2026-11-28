import J6R111KeptOwnerFlowGroupFirstDriver
import J6R111KeptOwnerFlowRunRoot
import J6R12IntegralDirectPrinted
import J6R34OfficialGatewayCore

/-! The actual group Meter of the retained interpreter. Arithmetic
correctness follows from the source sweep and live owner reads, not
from equality of fees with the legacy wrapper. -/
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
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R34OfficialGateway
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 440000
set_option diagnostics true
set_option diagnostics.threshold 1000
set_option pp.maxSteps 1200
set_option maxRecDepth 6000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams J6R24MeteredRecursion.Frame.decode J6R111KeptOwnerFlow.runRetained
set_option allowUnsafeReducibility true in
attribute [local irreducible] J6R32RootGeneratedRegistryInputs.exteriorChild
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local instance rootFlowEdgeFirstValue : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
  (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge


variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (head : OwnsHeader X.header.result B)
variable (first : FirstSource X M) (D : KeptDrivers X M rank)
variable (E : ExteriorLabels X M first rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base) (basePos : 0<base)
variable (valid : ReadyOnStack (borns M) B) (live : IsLive (X.seed pad) B)
variable (zeros : ZeroSourceAgreement X M B)
open J6R21Leaf

variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (labels : LabelWitness X
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
    w (first.make w).result.site (first.make w).result.owners)

private theorem firstJobAgrees :
    (first.make w).result.site.birth.job=
      (borns M (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
          (exteriorChild G ell X.centre X.sample X.group)) w).job := by
  let p : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group) := .root
  have same : (first.make w).result.site=sourceState M p w := congrArg Meter.result (first.exact w)
  exact congrArg (fun Z : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad)=>Z.birth.job) same

include boot gateWidth basePos valid live zeros in
theorem retained_first_child_run_decodes_the_actual_source :
    decodeFirstBlock (T:=T) X w (retainedFirstRun X M B first D retire w labels).result.1 =
      firstChildSourceValue (sel:=sel) X w := by
  let p : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group) := .root
  let x := retainedFirstInvocation X M B first w labels
  have job := firstJobAgrees X M first w
  have bank : x.entry.bank=stackBank (borns M) B (.step x.path x.slot) :=
    congrArg (afterOne B) job
  have physical := run_retained_decodes_the_same_printed_physical_host X M D retire B gate boot
    gateWidth basePos valid live zeros x bank
  unfold decodeFirstBlock firstChildSourceValue retainedFirstRun firstChildFrame
  dsimp only [x, retainedFirstInvocation, KeptInvocation.call] at physical ⊢
  set_option pp.explicit true in
  trace_state
  exact physical

include boot gateWidth basePos valid live zeros in
theorem one_retained_first_child_decodes_the_actual_source
    (bad : Meter (Block (firstChildFrame (T:=T) X w) ell)) :
    decodeFirstBlock (T:=T) X w (firstPaidBlock (T:=T) X M B first D retire w labels bad) =
      firstChildSourceValue (sel:=sel) X w := by
  let p : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group) := .root
  have job := firstJobAgrees X M first w
  have legal : JobsReady B [(first.make w).result.site.birth.job] :=
    Eq.mpr (congrArg (fun J : PageJob f ell key prec tw bw (pageKeyWidth m+pad)=>JobsReady B [J]) job) (valid p w)
  rw [first_scope_returns_the_actual_child_word X M B first D retire w labels bad legal]
  exact retained_first_child_run_decodes_the_actual_source X M B first D retire gate boot
    gateWidth basePos valid live zeros w labels

#print axioms retained_first_child_run_decodes_the_actual_source
#print axioms one_retained_first_child_decodes_the_actual_source
end
end J6R111KeptOwnerFlow

