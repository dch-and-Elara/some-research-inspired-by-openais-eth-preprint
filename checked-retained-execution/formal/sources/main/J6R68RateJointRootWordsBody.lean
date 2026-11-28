import J6R68RateJointRootWordsMount
import J6R55BootBodiesFactory

/-! The root handle lookup and replay use the true first root keys and selected
layout. The outer handle read and the inner producer debits are separate.
Neither the underlying lane writer nor the source atlas is run twice. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R26DescriptorTree J6R32StatefulArithmetic J6R33GeneratedChildSite J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R58BootScope J6R57ScopeFee J6R30ProducedGateRegistry
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 6500000
set_option maxSynthPendingDepth 16
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "TicketAt" => (fun w : RootSlot=>(Path.root : Path sel Ext Ext).ticket w)

variable (K : ResidentFirstTemplates X pad T) (L : BootLaneTape X gate pad)

def firstBodiesFromCheckedRootWords : FirstBodyProgram X gate pad T :=
  firstBodiesFromSameResident (sel:=sel) (T:=T) X gate pad L (paidRootTemplate X pad K)
    (paid_root_template_keeps_the_receiving_order X pad K)

theorem actual_first_body_word_price_not_double_charged
    (keyPositive : 0<key) (keyRoom : X.issue.result.val+1<2^key)
    (w : RootSlot) :
    let A := firstBodiesFromCheckedRootWords X gate pad K L
    let F := bodyAtActualSlot X gate pad A w
    F.result.issued=increment X.issue.result ∧
      measuredWordProducers F.result=firstReplayTariff (K.template w) (13*key+4)+4 ∧
      F.steps=(paidRootTemplate X pad K w).steps+
        (readFirstPhysical X gate pad A.lanes (A.seats w)).steps+4 := by
  let A := firstBodiesFromCheckedRootWords X gate pad K L
  let P := paidRootTemplate X pad K w
  let F := bodyAtActualSlot X gate pad A w
  have r := (paid_root_template_uses_exact_handle_and_key X pad K w).1
  have meter : measuredWordProducers P.result=firstReplayTariff (K.template w) (13*key+4) := by
    change measuredWordProducers (paidRootTemplate X pad K w).result=_
    rw [r,true_first_replayed_native_fields_fee,(increment_exact keyPositive X.issue.result keyRoom).2]
  have actual : measuredWordProducers F.result=measuredWordProducers P.result+4 := by
    change P.result.issued.steps+((P.result.native.steps+0+4)+P.result.physical.steps+
      P.result.words.steps+4)=P.result.issued.steps+(P.result.native.steps+P.result.physical.steps+
      P.result.words.steps+4)+4
    omega
  exact ⟨rfl,actual.trans (congrArg (·+4) meter),rfl⟩

#print axioms firstBodiesFromCheckedRootWords
#print axioms actual_first_body_word_price_not_double_charged
end
end J6R68RateJoint.RootWords

