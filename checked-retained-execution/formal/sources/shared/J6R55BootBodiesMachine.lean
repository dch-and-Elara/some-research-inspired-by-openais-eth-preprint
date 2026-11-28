import J6R55BootBodiesOccurrence
import J6R51OnlineCore

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
local notation "TicketAt" => (fun w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)=>(Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)

structure FirstBodyProgram (T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf) where
  lanes : BootLaneTape X gate pad
  width : (Plan sel).Slot Ext→ℕ
  old : ∀ w : (Plan sel).Slot Ext, Meter (OccurrenceInput T (TicketAt w) key prec tw bw Pg)
  seats : ∀ w : (Plan sel).Slot Ext,
    TerminalSeats X sel (ticketReady T (TicketAt w)) (TicketAt w).centerAt (width w)

variable (A : FirstBodyProgram X gate pad T)

def bodyAtActualSlot (slot : (Plan sel).Slot Ext) :
    Meter (OccurrenceInput T (TicketAt slot) key prec tw bw Pg) :=
  bootOccurrence X gate pad slot (A.old slot) A.lanes (A.seats slot)

theorem every_produced_first_slot_has_original_body
    (w : (Plan sel).Slot Ext) (h : Port E) :
    ((compileOccurrence (bodyAtActualSlot X gate pad A w).result).native.physical.record h).body=
      (initialPayload X gate pad h).2 :=
  true_first_slot_body_emitted X gate pad w (A.old w) A.lanes (A.seats w) h

variable {rate : ℕ}

/-- This is a whole input identity for a genuinely attached body
producer, not a hypothesis on any .record.body projection. -/
theorem source_body_of_attached_initial (M : OnlineMachine T key prec tw bw Pg rate)
    (attached : ∀ w : (Plan sel).Slot Ext,(M.initial w).result.input=(bodyAtActualSlot X gate pad A w).result)
    (w : (Plan sel).Slot Ext) (h : Port E) :
    ((M.initial w).result.birth.native.physical.record h).body=(initialPayload X gate pad h).2 := by
  change ((compileOccurrence (M.initial w).result.input).native.physical.record h).body=_
  rw [attached w]
  exact every_produced_first_slot_has_original_body X gate pad A w h

#print axioms bodyAtActualSlot
#print axioms every_produced_first_slot_has_original_body
#print axioms source_body_of_attached_initial
end
end J6R55BootBodies
