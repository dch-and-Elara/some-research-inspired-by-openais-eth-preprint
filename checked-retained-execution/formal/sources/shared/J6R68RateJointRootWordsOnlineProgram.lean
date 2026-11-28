import J6R68RateJointRootWordsOnlineHandle
import J6R55BootBodiesFactory

/-! Assemble an actual R55 first-body callback from one separately
metered source handle on demand. There is no single all-slot table. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R57ScopeFee J6R30ProducedGateRegistry J6R50SourceProducer
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 12
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
variable (L : BootLaneTape X gate pad)
variable (make : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  Meter (FirstSlotBook (r:=exteriorChild G ell X.centre X.sample X.group) (sel:=sel) T key prec tw bw (pageKeyWidth m+pad) w))
variable (order : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),(make w).result.datum.geometry.edges=orderedExteriorEdges X)

include order in
theorem selected_first_receiving_order (w : RootSlot) :
    (loadSelectedFirst (T:=T) (w:=w) (make w) X.issue.result).result.geometry.edges=orderedExteriorEdges X := by
  rw [(actual_selected_first_handle_partial_fee (make w) X.issue.result).1]
  exact (replay_first_input_has_the_same_selected_source (make w).result.datum
    (increment X.issue.result)).2.2.2.2.1.trans (order w)

def firstBodiesFromSelectedHandles : FirstBodyProgram X gate pad T :=
  firstBodiesFromSameResident (sel:=sel) (T:=T) X gate pad L
    (fun w=>loadSelectedFirst (T:=T) (w:=w) (make w) X.issue.result)
    (selected_first_receiving_order X pad make order)

theorem firstBodiesFromSelectedHandles_uses_exact_paid_operation (w : RootSlot) :
    (firstBodiesFromSelectedHandles X gate pad L make order).old w =
      loadSelectedFirst (T:=T) (w:=w) (make w) X.issue.result := rfl

#print axioms firstBodiesFromSelectedHandles_uses_exact_paid_operation
#print axioms selected_first_receiving_order
#print axioms firstBodiesFromSelectedHandles
end
end J6R68RateJoint.RootWords
