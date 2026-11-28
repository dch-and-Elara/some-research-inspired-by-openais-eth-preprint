import J6R68RateJointRootWordsHandle
import J6R58BootScopeResidentProgram

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
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 16
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "TicketAt" => (fun w : RootSlot=>(Path.root : Path sel Ext Ext).ticket w)

variable (K : ResidentFirstTemplates X pad T)

def paidRootTemplate (w : RootSlot) : Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg) :=
  recopyFirstHandle (T:=T) K.raw (K.keys w) w (K.template w) (K.hit w) X.issue.result

theorem paid_root_template_uses_exact_handle_and_key (w : RootSlot) :
    let F := paidRootTemplate X pad K w
    F.result=replayFirstInput (K.template w) (increment X.issue.result) ∧
    F.steps≤locateFee K.keyWidth K.raw.length+3*K.keyWidth+5 := by
  let I := fun w : RootSlot=>OccurrenceInput T (TicketAt w) key prec tw bw Pg
  have H := checked_boot_handle_retains_actual_source (T:=I)
    K.raw (K.keys w) w (K.template w) (K.hit w)
  refine ⟨?_,H.2⟩
  exact congrArg (fun I₀ : I w=>replayFirstInput I₀ (increment X.issue.result)) H.1

theorem paid_root_template_keeps_the_receiving_order (w : RootSlot) :
    (paidRootTemplate X pad K w).result.geometry.edges=orderedExteriorEdges X := by
  rw [(paid_root_template_uses_exact_handle_and_key X pad K w).1]
  have H := replay_first_input_has_the_same_selected_source (K.template w) (increment X.issue.result)
  exact H.2.2.2.2.1.trans (K.order w)

#print axioms paid_root_template_uses_exact_handle_and_key
#print axioms paid_root_template_keeps_the_receiving_order
end
end J6R68RateJoint.RootWords
