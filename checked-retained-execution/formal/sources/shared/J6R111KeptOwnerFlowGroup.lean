import J6R111KeptOwnerFlowGroupValue
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
set_option maxHeartbeats 2200000
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
local instance rootFlowEdgeGroupReceipt : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
  (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge


variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (head : OwnsHeader X.header.result B)
variable (first : FirstSource X M) (D : KeptDrivers X M rank)
variable (E : ExteriorLabels X M first rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

/-- The independently printed algebraic theorem omits a caller-provided
envelope comparison. Reconstruct its ambient synthesized instance here,
before introducing the interpreter's proof-side dictionary. -/
private def printedEnvelopeComparison
    (sel' : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (r' : Call (PhysicalHost f ell)) :
    DecidableEq (J6R10Reachable.Envelope (N sel') (Childs sel') r') := inferInstance

variable [envDec : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base) (basePos : 0<base)
variable (valid : ReadyOnStack (borns M) B) (live : IsLive (X.seed pad) B)
variable (zeros : ZeroSourceAgreement X M B)
variable (rootStops : ExteriorRootStops X M B)

def retainedPhysicalGroup
    (degree : 0<f.natDegree) :
    GroupReceipt (ell:=ell) G X.hf X.centre X.sample X.group where
  frame := retainedExteriorFrame (T:=T) X
  run := let done := runRetainedExterior X M B head first D E retire
         ⟨done.result.1,done.steps⟩
  truth := by
    let r := exteriorChild G ell X.centre X.sample X.group
    have interpret := retained_exterior_decodes_the_original_group_program X M B head first D E retire
      gate boot gateWidth basePos (fun {_} p w=>valid p w) live zeros rootStops
    have honest := J6R12Integral.printed_run_exact cfg sel r T.rootStable X.hf degree
    have final : exteriorSourceValue (sel:=sel) X = reduce r.prec f ell (r.host.contract X.hf) := by
      -- The independent algebraic theorem is stated with its classical
      -- envelope comparison; the running meter may use any such comparison.
      unfold exteriorSourceValue
      have compare : envDec = printedEnvelopeComparison sel r :=
        Subsingleton.elim _ _
      rw [compare]
      unfold printedEnvelopeComparison
      exact honest
    exact interpret.trans final

#print axioms retainedPhysicalGroup
end
end J6R111KeptOwnerFlow

