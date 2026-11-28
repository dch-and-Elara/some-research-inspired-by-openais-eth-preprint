import J6R111KeptOwnerFlowRunCorrect
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
set_option maxHeartbeats 9000000
set_option maxRecDepth 6000
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
local instance rootFlowEdgeFirstDriver : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
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

def descendFromFirst (entry : CapturedEntry X
    (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
      w (first.make w).result.site) :
    Meter (Block (T.frame (Path.step (.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)) w).reached) ell×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  runRetained X M D retire ⟨exteriorChild G ell X.centre X.sample X.group,.root,w,_,
    congrArg Meter.result (first.exact w),entry⟩

/-- The frame of the physically addressed first child. -/
def firstChildFrame (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    Frame f ((Plan sel).child (exteriorChild G ell X.centre X.sample X.group) w).prec :=
  T.frame (Path.step (.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)) w).reached

/-- The source word actually read from the billed first-child invocation. -/
def firstPaidBlock (bad : Meter (Block (firstChildFrame (T:=T) X w) ell)) :
    Block (firstChildFrame (T:=T) X w) ell :=
  (enterPaidFirst (Out:=Block (firstChildFrame (T:=T) X w) ell) X B retire w (first.make w)
    (descendFromFirst X M first D retire w) labels bad).result.1

/-- Fixed decoder, with all indices explicit to avoid recomputing a layout. -/
def decodeFirstBlock
    (x : Block (firstChildFrame (T:=T) X w) ell) :
    Box f ell ((Plan sel).child (exteriorChild G ell X.centre X.sample X.group) w).prec :=
  @J6R24MeteredRecursion.Frame.decode f ((Plan sel).child (exteriorChild G ell X.centre X.sample X.group) w).prec ell
    (firstChildFrame (T:=T) X w) x

/-- Correct comparison target at the very same printed child address. -/
def firstChildSourceValue (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    Box f ell ((Plan sel).child (exteriorChild G ell X.centre X.sample X.group) w).prec :=
  (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run
    ((Plan sel).child (exteriorChild G ell X.centre X.sample X.group) w)

/-- Enter the same received site, with its actually installed resources. -/
def retainedFirstInvocation : KeptInvocation X M :=
  let Y := (first.make w).result.site
  ⟨exteriorChild G ell X.centre X.sample X.group,.root,w,Y,congrArg Meter.result (first.exact w),
    ⟨(installResidentBank Y).result,afterOne B Y.birth.job,rfl,(first.make w).result.owners,labels⟩⟩

def retainedFirstRun : Meter (Block (firstChildFrame (T:=T) X w) ell×
    PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  runRetained X M D retire (retainedFirstInvocation X M B first w labels)

/-- The two charges are intentionally different; only the projection agrees. -/
theorem first_scope_returns_the_actual_child_word
    (bad : Meter (Block (firstChildFrame (T:=T) X w) ell))
    (legal : JobsReady B [(first.make w).result.site.birth.job]) :
    firstPaidBlock (T:=T) X M B first D retire w labels bad=
      (retainedFirstRun X M B first D retire w labels).result.1 := by
  have execution := the_paid_first_carrier_enters_one_live_resident_and_restores_parent
    (Out:=Block (firstChildFrame (T:=T) X w) ell) X B retire w (first.make w)
    (descendFromFirst X M first D retire w) labels bad legal
  have onlyWord := congrArg (fun z : Meter (Block (firstChildFrame (T:=T) X w) ell×
    PageBank f ell key prec tw bw (pageKeyWidth m+pad))=>z.result.1) execution
  exact onlyWord

#print axioms retainedFirstInvocation
#print axioms retainedFirstRun
#print axioms first_scope_returns_the_actual_child_word
#print axioms firstChildFrame
#print axioms firstPaidBlock
#print axioms decodeFirstBlock
#print axioms firstChildSourceValue
#print axioms descendFromFirst

end
end J6R111KeptOwnerFlow
