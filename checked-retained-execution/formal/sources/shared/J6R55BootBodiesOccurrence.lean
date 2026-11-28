import J6R55BootBodiesPhysical
import J6R48RawRouteOccurrence
import J6R50SourceProducerOnline

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
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer
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
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "first" => ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)
local notation "Pg" => (pageKeyWidth m+pad)
variable {b : ℕ}

def bootOccurrence (template : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b) :
    Meter (OccurrenceInput T first key prec tw bw Pg) :=
  let new := readFirstPhysical X gate pad L S
  let I := replaceOccurrencePhysical template.result ⟨new.result,0⟩
  ⟨I,template.steps+new.steps+4⟩

theorem true_first_slot_body_emitted
    (template : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b)
    (h : Port E) :
    ((compileOccurrence (bootOccurrence X gate pad w template L S).result).native.physical.record h).body=
      (initialPayload X gate pad h).2 := by
  have body := compiled_replaced_row_body template.result
    (⟨(readFirstPhysical X gate pad L S).result,0⟩ :
      Meter (PhysicalFile T first (rootHalfWidth m+1))) h
  exact body.trans (actual_first_physical_is_written X gate pad L S h).2.1

theorem actual_boot_occurrence_charges_raw_writer_once
    (template : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b) :
    let writer := readFirstPhysical X gate pad L S
    let start := bootOccurrence X gate pad w template L S
    let born := compileOccurrence start.result
    birthPhysical born=⟨rootHalfWidth m+1,writer.result⟩ ∧
    born.job.identifier=template.result.issued.result ∧
    born.job.immutable.payload.stamp.created.val=(first).child.prec ∧
    start.steps=template.steps+writer.steps+4 ∧
    born.issuance.steps=template.result.issued.steps+
      (template.result.native.steps+4+template.result.physical.steps+template.result.words.steps+4) := by
  let writer := readFirstPhysical X gate pad L S
  let raw : Meter (PhysicalFile T first (rootHalfWidth m+1)) := ⟨writer.result,0⟩
  have h := generated_occurrence_has_no_old_physical_input template.result raw
  exact ⟨h.1,h.2.1,h.2.2.1,rfl,h.2.2.2⟩

theorem replaced_boot_keeps_real_numeric_and_atlas_words
    (template : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b) :
    let start := (bootOccurrence X gate pad w template L S).result
    start.native.result.coordinates=template.result.native.result.coordinates ∧
      start.issued=template.result.issued ∧ start.physical=template.result.physical ∧
      start.words=template.result.words :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem replacing_a_template_cannot_supply_boot_body_bytes
    (U V : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b) :
    (bootOccurrence X gate pad w U L S).result.native.result.physical.raw=
      (bootOccurrence X gate pad w V L S).result.native.result.physical.raw := rfl

#print axioms bootOccurrence
#print axioms replacing_a_template_cannot_supply_boot_body_bytes
#print axioms true_first_slot_body_emitted
#print axioms actual_boot_occurrence_charges_raw_writer_once
#print axioms replaced_boot_keeps_real_numeric_and_atlas_words
end
end J6R55BootBodies
