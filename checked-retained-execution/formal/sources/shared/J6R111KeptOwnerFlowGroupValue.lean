import J6R111KeptOwnerFlowGroupFirstValue
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
set_option maxHeartbeats 4200000
set_option maxRecDepth 6000
set_option pp.maxSteps 1400
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams J6R24MeteredRecursion.Frame.decode
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
local instance rootFlowEdgeGroup : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
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
/-- The frame consumed by the same physical exterior meter. -/
def retainedExteriorFrame : Frame f (exteriorChild G ell X.centre X.sample X.group).prec :=
  T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).reached

def exteriorSourceValue : Box f ell (exteriorChild G ell X.centre X.sample X.group).prec :=
  (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run
    (exteriorChild G ell X.centre X.sample X.group)

def decodeExteriorWord (w : Block (retainedExteriorFrame (T:=T) X) ell) :
    Box f ell (exteriorChild G ell X.centre X.sample X.group).prec :=
  @J6R24MeteredRecursion.Frame.decode f (exteriorChild G ell X.centre X.sample X.group).prec ell
    (retainedExteriorFrame (T:=T) X) w

/-- Only the genuine nonrecursive stop is supplied here. All descendants
are interpreted by the retained execution, including positive leaves. -/
def ExteriorRootStops : Prop :=
  ∀ stop : (exteriorChild G ell X.centre X.sample X.group).edges≤
      (printedParams (f:=f) (ell:=ell) s).cutoff,
    decodeExteriorWord (T:=T) X (M.leafRoot stop B).result=exteriorSourceValue (sel:=sel) X

variable (rootStops : ExteriorRootStops X M B)

include boot gateWidth basePos valid live zeros rootStops in
theorem retained_exterior_decodes_the_original_group_program :
    decodeExteriorWord (T:=T) X (runRetainedExterior X M B head first D E retire).result.1=
      exteriorSourceValue (sel:=sel) X := by
  let sp := printedParams (f:=f) (ell:=ell) s
  let r := exteriorChild G ell X.centre X.sample X.group
  let path : Path sel r r := .root
  by_cases stop : r.edges≤sp.cutoff
  · unfold ExteriorRootStops at rootStops
    rw [runRetainedExterior,dif_pos stop]
    exact rootStops stop
  · let on := Nat.lt_of_not_ge stop
    let d := readyAtPath T path on
    let W := E.setup on
    let packed := selectedLayoutAndLabels W
    let taper := actual_path_taper T path on
    let A := prepare (bank:=T.bank) M.modeWidth (D.fit path on) taper.1 taper.2 X.hf
      D.masks.table (D.masks.covers path on) (readExterior X B head) ⟨packed.result.receipt,packed.steps⟩
    let makeLabels (w : (Plan sel).Slot r) :=
      useAlreadyEmittedLabels X path w (first.make w).result.site (first.make w).result.owners W packed.result rfl
        (first.make w).result.injective (E.order on w) (E.exactLabels on)
    let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (enterPaidFirst X B retire w (first.make w) (descendFromFirst X M first D retire w) (makeLabels w)
        (zeroM (T.bank (registerPrecision sp r t) (register_positive d t)).hp))
    have each (t : Center sp r) (z : Probe sp r) (β : NativeMenu (N sel) r t) (g : Fin 64) :
        (T.bank (registerPrecision sp r t) (register_positive d t)).decode (ell:=ell) (read t z β g).result=
        (sourceBlueprint sel r X.hf).program.run ((Plan sel).child r ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      let low := T.bank (registerPrecision sp r t) (register_positive d t)
      exact one_retained_first_child_decodes_the_actual_source X M B first D retire
        gate boot gateWidth basePos valid live zeros w (makeLabels w) (zeroM low.hp : Meter (Block low ell))
    let hp := reachable_positive T path.reached
    obtain ⟨_,_,value,truth⟩ := actual_active_decoded cfg sel r X.hf path.reached d T.rootStable
      A.result.proofView.prior hp T.vPositive read each
    have stopped : ¬(exteriorChild G ell X.centre X.sample X.group).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff := stop
    simp only [runRetainedExterior,dif_neg stopped]
    unfold decodeExteriorWord exteriorSourceValue
    change (T.bank r.prec hp).decode (ell:=ell) (A.result.eval M.modeWidth hp T.vPositive X.hf read).result=_
    rw [A.result.exact_sweep_matches_its_own_proof_view,active_stream_value A.result.proofView M.modeWidth hp T.vPositive X.hf read,value]
    exact truth

#print axioms retainedExteriorFrame
#print axioms exteriorSourceValue
#print axioms ExteriorRootStops
#print axioms retained_exterior_decodes_the_original_group_program
end
end J6R111KeptOwnerFlow

