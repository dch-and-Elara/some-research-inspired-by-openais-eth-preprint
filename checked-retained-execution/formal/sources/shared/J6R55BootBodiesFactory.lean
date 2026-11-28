import J6R55BootBodiesMachine
import J6R55BootBodiesResident

/-! Feed the actually built file to the original occurrence compiler
at every real first slot. The raw writer is paid eagerly in the boot
meter; its fee is not added again to the nested native issuance. -/
namespace J6R55BootBodies
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23000000
set_option maxRecDepth 3700
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Pg" => (pageKeyWidth m+pad)
local notation "TicketAt" => (fun w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)=>
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
    (exteriorChild G ell X.centre X.sample X.group)).ticket w)
local notation "A" =>
  (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
    (exteriorChild G ell X.centre X.sample X.group).depth)

/-- If the existing chart already reports seats in the exact source
order, reuse its paid array. Neither an independent chart nor a
second seat-preparation meter is needed. -/
def firstBodiesFromSameResident
    (L : BootLaneTape X gate pad)
    (baseWords : ∀ w : (Plan sel).Slot Ext, Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg))
    (agree : ∀ w,(baseWords w).result.geometry.edges=orderedExteriorEdges X) :
    FirstBodyProgram X gate pad T where
  lanes := L
  width w := ((baseWords w).result.q-A)+13*A
  old := baseWords
  seats w := actualSameOrderSeats X pad w (baseWords w).result (agree w)

theorem resident_factory_first_slot_actual
    (L : BootLaneTape X gate pad)
    (baseWords : ∀ w : (Plan sel).Slot Ext, Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg))
    (agree : ∀ w,(baseWords w).result.geometry.edges=orderedExteriorEdges X)
    (w : (Plan sel).Slot Ext) (h : Port E) :
    let I := (baseWords w).result
    let A₀ := firstBodiesFromSameResident X gate pad L baseWords agree
    let boot := bodyAtActualSlot X gate pad A₀ w
    ((compileOccurrence boot.result).native.physical.record h).body=(initialPayload X gate pad h).2 ∧
      boot.result.issued=I.issued ∧
      boot.steps=(baseWords w).steps+(
        8+((orderedExteriorEdges X).map (fun e=>bootPairFee (laneView X gate pad e)
          (physicalSeatField (packing sel (ticketReady T (TicketAt w)))
            (centerIndex (ticketReady T (TicketAt w)) (TicketAt w).centerAt)
            (childPageKey (I.q-A)) e))).sum)+4 := by
  let A₀ := firstBodiesFromSameResident X gate pad L baseWords agree
  exact ⟨every_produced_first_slot_has_original_body X gate pad A₀ w h,rfl,
    congrArg (fun s=>(baseWords w).steps+s+4)
      (actual_same_order_seats_no_second_preparation X gate pad w (baseWords w).result (agree w) L h).2⟩

#print axioms firstBodiesFromSameResident
#print axioms resident_factory_first_slot_actual
end
end J6R55BootBodies
