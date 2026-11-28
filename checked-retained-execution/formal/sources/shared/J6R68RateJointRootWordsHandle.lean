import J6R68RateJointRootWordsInput
import J6R58BootScopeResident

/-! One paid real first-ticket handle. This module leaves the boot body
assembly separate from the actual reference lookup and primitive copy. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R32StatefulArithmetic J6R34RootAtlas J6R58BootScope J6R57ScopeFee
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page handle : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Slot" => ((Plan sel).Slot r)
local notation "TicketAt" => (fun w : Slot=>(Path.root : Path sel r r).ticket w)
local notation "InputAt" => (fun w : Slot=>OccurrenceInput T (TicketAt w) key prec tw bw page)

def recopyFirstHandle (rows : List (RefRow handle (Sigma InputAt))) (addr : Word handle)
    (w : Slot) (I : InputAt w) (hit : (locate addr rows).result=some ⟨w,I⟩)
    (last : Word key) : Meter (InputAt w) :=
  let H := checkedBootHandle (T:=InputAt) rows addr w I hit
  ⟨replayFirstInput H.result (increment last),H.steps⟩

theorem actual_first_handle_and_source_costs
    (rows : List (RefRow handle (Sigma InputAt))) (addr : Word handle)
    (w : Slot) (I : InputAt w) (hit : (locate addr rows).result=some ⟨w,I⟩)
    (last : Word key) (keyPositive : 0<key) (keyRoom : last.val+1<2^key) :
    let F := recopyFirstHandle rows addr w I hit last
    F.result=replayFirstInput I (increment last) ∧
    F.steps≤locateFee handle rows.length+3*handle+5 ∧
    measuredWordProducers F.result=firstReplayTariff I (13*key+4) := by
  let F := recopyFirstHandle rows addr w I hit last
  obtain ⟨h,fee⟩ := checked_boot_handle_retains_actual_source (T:=InputAt) rows addr w I hit
  have same : F.result=replayFirstInput I (increment last) :=
    congrArg (fun x : InputAt w=>replayFirstInput x (increment last)) h
  have p := true_first_replayed_native_fields_fee I (increment last)
  rw [(increment_exact keyPositive last keyRoom).2] at p
  exact ⟨same,fee,(congrArg measuredWordProducers same).trans p⟩

#print axioms recopyFirstHandle
#print axioms actual_first_handle_and_source_costs
end
end J6R68RateJoint.RootWords

