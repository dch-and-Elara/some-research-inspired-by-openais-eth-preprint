import J6R75OuterTimeGroup
import J6R36SharedGatewayDelta

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 14000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Actual 64-group public slot. Pay one head, use its returned head
for each real R57-addressed R68 group invocation, perform the native
receiving-frame copies, and fold in the original group order. -/
namespace J6R75OuterTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R33OriginalJ6 J6R68AbsolutePrescribed
open J6R63Active J6R62ActivePrep J6R14ZeroMode

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (R : RawGroupPlans D S pad prior cfg rate cw)
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)

variable (frame : Frame f (J6SourcePrecision.printed m base))
variable (hv : 0<ell)

/-- The exterior client in R36 always dispatches the prescribed probe.
This implementation uses the literal R57 submit, which reloads it and
still runs the paid server gate. Outside that legal image this adapter
does not promise the behavior of a general raw-input server. -/
def paidRawSlot : SlotProgram (ell:=ell) (F:=frame) G :=
  fun i j _ =>
    let E := SiteFrame G ell frame i
    let H := prepareHead W i j
    let collect := foldM E.hp E.sizePos hv (fun g : Fin 64=>
      frameCopy D.hf (actualGroupFrame D S pad prior R i j g) E
        (paidSourceGroup D S pad prior R sync reserved i j g H.result rfl)) (groupOrder 64)
    ⟨collect.result,H.steps+collect.steps+3⟩

theorem paid_raw_slot_recovers_the_original_completed_product
    (i : Centre) (j : Sample) (raw : List Bool) :
    let H := prepareHead W i j
    let complete := completedGroups G D.hf frame hv i j
      (fun g=>verifiedSourceGroup D S pad prior R sync reserved i j g H.result rfl)
    paidRawSlot D S pad prior R sync reserved frame hv i j raw=
      ⟨complete.result,H.steps+complete.steps+3⟩ := rfl

#print axioms paidRawSlot
#print axioms paid_raw_slot_recovers_the_original_completed_product
end
end J6R75OuterTime

