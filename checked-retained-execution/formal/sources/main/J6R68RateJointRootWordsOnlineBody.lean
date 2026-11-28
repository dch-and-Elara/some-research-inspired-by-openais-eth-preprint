import J6R68RateJointRootWordsOnlineHandle
import J6R48RawRouteOccurrence

/-! This is the first replacement step in R55's bootOccurrence, made
from one per-event handle and the genuinely paid physical writer.
The writer's debit belongs only to the outer Meter. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R34RootAtlas J6R32StatefulArithmetic J6R57ScopeFee
open J6R33StatefulArithmeticPage J6R48RawRoute
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option maxHeartbeats 6800000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page port : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Slot" => ((Plan sel).Slot r)
local notation "Here" => (Path.root : Path sel r r)
local notation "TicketAt" => (fun w : Slot=>(Here).ticket w)

def replaceSelectedFirst {w : Slot}
    (paid : Meter (FirstSlotBook T key prec tw bw page w)) (lastKey : Word key)
    (physical : Meter (PhysicalFile T (TicketAt w) port)) :
    Meter (OccurrenceInput T (TicketAt w) key prec tw bw page) :=
  let I := loadSelectedFirst paid lastKey
  ⟨replaceOccurrencePhysical I.result ⟨physical.result,0⟩,I.steps+physical.steps+4⟩

theorem selected_first_replacement_bills_both_real_phases {w : Slot}
    (paid : Meter (FirstSlotBook T key prec tw bw page w)) (sourceKey : Word key)
    (physical : Meter (PhysicalFile T (TicketAt w) port))
    (pos : 0<key) (room : sourceKey.val+1<2^key) :
    let body := replaceSelectedFirst paid sourceKey physical
    let job := compileOccurrence body.result
    body.steps≤paid.steps+selectedFirstHandleFee paid.result+3+physical.steps+4 ∧
      job.job.identifier=(increment sourceKey).result ∧
      job.issuance.steps=firstReplayTariff paid.result.datum (13*key+4)+4 := by
  let original := loadSelectedFirst paid sourceKey
  let body := replaceSelectedFirst paid sourceKey physical
  have H := actual_selected_first_issuance_tariff paid sourceKey pos room
  have h := (actual_selected_first_handle_partial_fee paid sourceKey).2
  have inserted : measuredWordProducers body.result=measuredWordProducers original.result+4 := by
    change original.result.issued.steps+((original.result.native.steps+0+4)+original.result.physical.steps+
      original.result.words.steps+4)=original.result.issued.steps+(original.result.native.steps+
      original.result.physical.steps+original.result.words.steps+4)+4
    omega
  have ik : body.result.issued=increment sourceKey := H.1
  exact ⟨Nat.add_le_add_right (Nat.add_le_add_right h _) _,
    (occurrence_identity body.result).1.trans (congrArg (fun m : Meter (Word key)=>m.result) ik),
    (compiled_occurrence_priced_by_actual_producers_and_chart body.result).1.trans
      (inserted.trans (congrArg (·+4) H.2))⟩

#print axioms selected_first_replacement_bills_both_real_phases
end
end J6R68RateJoint.RootWords

