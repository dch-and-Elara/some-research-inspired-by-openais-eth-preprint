import J6R68RateJointRootWordsHandle

/-! The first entrance need not hold a whole menu of source references.
The provider is measured before this one selected handle is consumed.
Only a hit for the currently addressed slot is required. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R34RootAtlas J6R32StatefulArithmetic J6R57ScopeFee
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4100
set_option maxHeartbeats 7400000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Slot" => ((Plan sel).Slot r)
local notation "Here" => (Path.root : Path sel r r)
local notation "InputAt" => (fun w : Slot=>OccurrenceInput T ((Here).ticket w) key prec tw bw page)

/-- A measured read provider for the current address: the table may
have irrelevant rows and must not satisfy coverage for any other slot. -/
structure FirstSlotBook (T : Prepared cfg sel r hf) (key prec tw bw page : ℕ) (w : Slot) where
  width : ℕ
  rows : List (RefRow width (Sigma (fun x : Slot=>OccurrenceInput T ((Here).ticket x) key prec tw bw page)))
  address : Word width
  datum : OccurrenceInput T ((Here).ticket w) key prec tw bw page
  hit : (locate address rows).result=some ⟨w,datum⟩

def selectedFirstHandleFee {w : Slot}
    (B : FirstSlotBook T key prec tw bw page w) : ℕ :=
  locateFee B.width B.rows.length+3*B.width+5

def loadSelectedFirst {w : Slot}
    (build : Meter (FirstSlotBook T key prec tw bw page w)) (last : Word key) :
    Meter (InputAt w) :=
  let B := build.result
  let got := recopyFirstHandle (T:=T) B.rows B.address w B.datum B.hit last
  ⟨got.result,build.steps+got.steps+3⟩

theorem actual_selected_first_handle_partial_fee {w : Slot}
    (build : Meter (FirstSlotBook T key prec tw bw page w)) (last : Word key) :
    let I := loadSelectedFirst build last
    I.result=replayFirstInput build.result.datum (increment last) ∧
      I.steps ≤ build.steps+selectedFirstHandleFee build.result+3 := by
  let B := build.result
  let I := loadSelectedFirst build last
  obtain ⟨same,fee⟩ := J6R58BootScope.checked_boot_handle_retains_actual_source
    (T:=InputAt) B.rows B.address w B.datum B.hit
  exact ⟨congrArg (fun x : InputAt w=>replayFirstInput x (increment last)) same,
    Nat.add_le_add_right (Nat.add_le_add_left fee build.steps) 3⟩

theorem actual_selected_first_issuance_tariff {w : Slot}
    (build : Meter (FirstSlotBook T key prec tw bw page w)) (last : Word key)
    (pos : 0<key) (room : last.val+1<2^key) :
    let I := loadSelectedFirst build last
    I.result.issued=increment last ∧
      measuredWordProducers I.result=firstReplayTariff build.result.datum (13*key+4) := by
  dsimp only
  rw [(actual_selected_first_handle_partial_fee build last).1]
  refine ⟨rfl,?_⟩
  rw [true_first_replayed_native_fields_fee,(increment_exact pos last room).2]

#print axioms actual_selected_first_handle_partial_fee
#print axioms actual_selected_first_issuance_tariff
end
end J6R68RateJoint.RootWords

