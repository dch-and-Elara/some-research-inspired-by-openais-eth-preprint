import J6R114SelectedOperandsFirstSource
import J6R116ReadyRetainedPayload

/-! Use the held R114 source values to construct the exact R116 entry
payload. Alignment is a proof-only reindexing back to the same
resident admission. No descriptor, publisher, or old driver reruns. -/
namespace J6R116ReadyFromHeld
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R62ActivePrep J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R108FinalDriver J6R111KeptOwnerFlow J6R114SelectedOperands
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 3800000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}

local instance heldReadyRootDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)



variable (rootInj : Function.Injective rootName)
variable (sync : prior.synced)
variable (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)



variable (R : PublicOperandReceipt (W:=W) D pad i j g gate root T rate)
local notation "Ext" => (exteriorChild G ell R.observed.centre R.observed.sample R.observed.group)
local notation "F" => (preparedAtOtherSource R.observed (literalSite W D i j g) R.same T)
local notation "M" => (machineOnHeldOperandsWithRealCode D pad i j g gate root rootInj R)
local notation "First" => (firstOwnerSourceOnTheSameHeldOperands D pad i j g gate root rootInj R)

open J6R111KeptOwnerFlow

/-- The remaining real retained inputs. The machine and the first
owner producer are not supplied. The code, boot and exact first
mount come from the receipt of the actual prior producer. -/
structure RemainingRetainedInputs where
  rank : ℕ
  drivers : KeptDrivers R.observed (M) rank
  exterior : ExteriorLabels R.observed (M) (First) rank
  retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ
  gateWidth : gate.created.val=base
  basePositive : 0<base
  valid : ReadyOnStack (borns (M)) R.bank
  zeroBranch : ZeroSourceAgreement R.observed (M) R.bank
  exteriorStop : ∀ stop : (Ext).edges≤(printedParams (f:=f) (ell:=ell) (physicalSize m native)).cutoff,
    ((F).frame (Path.root : Path (G.selector ell) (Ext) (Ext)).reached).decode
      ((M).leafRoot stop R.bank).result=
    (sourceBlueprint (G.selector ell) (Ext) R.observed.hf).program.run (Ext)
  degreePositive : 0<f.natDegree

variable (A : ResidentAdmissionCarry (W:=W) D pad)
variable (siteSame : R.observed=A.site) (bankSame : R.bank=A.receipt.1)

/-- A temporary alignment index only. Its site and bank are actual
already-held values. Neither `entrySource` nor `submitResidentRow`
appears as an operation. -/
def receiptIndexForTheHeldSource : ResidentAdmissionCarry (W:=W) D pad :=
  ⟨A.row,R.observed,(R.bank,A.receipt.2),siteSame.trans A.oneSite⟩

include bankSame in
theorem receipt_index_is_the_same_old_admission :
    receiptIndexForTheHeldSource D pad i j g gate root R A siteSame=A := by
  cases A with
  | mk row observed out one =>
    cases out with
    | mk b ok =>
      dsimp only at siteSame bankSame
      cases siteSame
      cases bankSame
      rfl

/-- The prepared data on those precise held values before the index
is cast back to the original admission. -/
def readyAtTheHeldIndex
    (inputs : RemainingRetainedInputs D pad i j g gate root rootInj R) :
    ReadyRetainedPayload (receiptIndexForTheHeldSource D pad i j g gate root R A siteSame) where
  size := physicalSize m native
  constant := 2
  rate := rate
  rank := inputs.rank
  bounds := G.bounds
  selector := G.selector ell
  prepared := (F)
  machine := (M)
  first := (First)
  drivers := inputs.drivers
  exterior := inputs.exterior
  retire := inputs.retire
  gate := gate
  boot := held_machine_has_the_actual_printed_boot D pad i j g gate root rootInj R
  gateWidth := inputs.gateWidth
  basePositive := inputs.basePositive
  valid := inputs.valid
  zeroBranch := inputs.zeroBranch
  exteriorStop := inputs.exteriorStop
  degreePositive := inputs.degreePositive

def readyFromActualHeldOperands
    (inputs : RemainingRetainedInputs D pad i j g gate root rootInj R) :
    ReadyRetainedPayload A :=
  (receipt_index_is_the_same_old_admission D pad i j g gate root R A siteSame bankSame) ▸
    readyAtTheHeldIndex D pad i j g gate root rootInj R A siteSame inputs

theorem actual_held_retained_payload_has_source_scale
    (inputs : RemainingRetainedInputs D pad i j g gate root rootInj R) :
    let actual := readyFromActualHeldOperands D pad i j g gate root rootInj R A siteSame bankSame inputs
    actual.size=physicalSize m native ∧ actual.constant=2 ∧ HEq actual.selector (G.selector ell) := by
  let old := readyAtTheHeldIndex D pad i j g gate root rootInj R A siteSame inputs
  let eq := receipt_index_is_the_same_old_admission D pad i j g gate root R A siteSame bankSame
  have transport {L K : ResidentAdmissionCarry (W:=W) D pad} (h : L=K)
      (P : ReadyRetainedPayload L) :
      let t : ReadyRetainedPayload K := h ▸ P
      t.size=P.size ∧ t.constant=P.constant ∧ HEq t.selector P.selector := by
    cases h
    exact ⟨rfl,rfl,HEq.rfl⟩
  exact transport eq old

theorem transport_keeps_the_actual_machine_and_first_producer
    {L K : ResidentAdmissionCarry (W:=W) D pad} (h : L=K) (Q : ReadyRetainedPayload L) :
    let t : ReadyRetainedPayload K := h ▸ Q
    HEq t.machine Q.machine ∧ HEq t.first Q.first := by
  cases h
  exact ⟨HEq.rfl,HEq.rfl⟩

theorem ready_on_the_held_bank_keeps_the_exact_R102_machine_and_first
    (inputs : RemainingRetainedInputs D pad i j g gate root rootInj R) :
    let A' := readyFromActualHeldOperands D pad i j g gate root rootInj R A siteSame bankSame inputs
    HEq A'.machine (M) ∧ HEq A'.first (First) :=
  transport_keeps_the_actual_machine_and_first_producer D pad
    (receipt_index_is_the_same_old_admission D pad i j g gate root R A siteSame bankSame)
    (readyAtTheHeldIndex D pad i j g gate root rootInj R A siteSame inputs)

#print axioms receipt_index_is_the_same_old_admission
#print axioms readyAtTheHeldIndex
#print axioms readyFromActualHeldOperands
#print axioms actual_held_retained_payload_has_source_scale
#print axioms ready_on_the_held_bank_keeps_the_exact_R102_machine_and_first
end
end J6R116ReadyFromHeld

