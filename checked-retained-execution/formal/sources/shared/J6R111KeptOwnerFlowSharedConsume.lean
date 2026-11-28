import J6R111KeptOwnerFlowSharedAdmission
import J6R111KeptOwnerFlowGroup

/-! The data operands are the site and bank actually returned by the
paid admission. The prepared drive and liveness are typed on those
operands; no call to `literalSite`, emitAt, or install is made here. -/
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
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R34OfficialGateway J6R54PublicFamily
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2300000
set_option maxRecDepth 6000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj kp prec tw bw : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {Cpt : Compiled G ell q ro co de prec kp bw}
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable (admitted : ResidentAdmissionCarry (W:=W) Cpt pad)
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell admitted.site.centre admitted.site.sample admitted.site.group) admitted.site.hf}
variable (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (head : OwnsHeader admitted.site.header.result admitted.receipt.1)
variable (first : FirstSource admitted.site M) (D : KeptDrivers admitted.site M rank)
variable (E : ExteriorLabels admitted.site M first rank)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell admitted.site.centre admitted.site.sample admitted.site.group))]
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (boot : ExactPrintedBoot admitted.site M gate) (gateWidth : gate.created.val=base) (basePos : 0<base)
variable (valid : ReadyOnStack (borns M) admitted.receipt.1)
variable (live : IsLive (admitted.site.seed pad) admitted.receipt.1)
variable (zeros : ZeroSourceAgreement admitted.site M admitted.receipt.1)
variable (rootStops : ExteriorRootStops admitted.site M admitted.receipt.1)

variable (degree : 0<f.natDegree)

/-- No further group site construction or registry mount is performed. -/
def consumeAdmittedKeptGroup :
    GroupReceipt (ell:=ell) G admitted.site.hf admitted.site.centre admitted.site.sample admitted.site.group :=
  retainedPhysicalGroup admitted.site M admitted.receipt.1 head first D E retire
    gate boot gateWidth basePos (fun {_} p w=>valid p w) live zeros rootStops degree

theorem admitted_group_is_exactly_the_run_on_the_returned_site_and_bank :
    let run := runRetainedExterior admitted.site M admitted.receipt.1 head first D E retire
    (consumeAdmittedKeptGroup admitted M head first D E retire gate boot gateWidth basePos valid live zeros rootStops degree).run=
      ⟨run.result.1,run.steps⟩ := rfl

#print axioms consumeAdmittedKeptGroup
#print axioms admitted_group_is_exactly_the_run_on_the_returned_site_and_bank
end
end J6R111KeptOwnerFlow

