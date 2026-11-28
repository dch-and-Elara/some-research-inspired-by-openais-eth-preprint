import J6R55SelectedPeakBootWriter
import J6R55BootBodiesOccurrence

/-! Track the very same written raw payload into the first genuine
compiled occurrence. The meter charges that writer outside issuance
exactly once, and its selected buffers are not a second per-slot native
physical tape. This does not supply template numeric/atlas inputs. -/
namespace J6R55SelectedPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion
open J6R50SourceProducer J6R55BootBodies J6R54PeakInput

set_option quotPrecheck false
set_option autoImplicit false
set_option maxRecDepth 4050
set_option maxHeartbeats 24600000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "first" => ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group)).ticket w)
local notation "Pg" => (pageKeyWidth m+pad)
variable {b : ℕ}

theorem same_first_native_occurrence_has_the_accounted_boot_file
    (template : Meter (OccurrenceInput T first key prec tw bw Pg))
    (L : BootLaneTape X gate pad) (S : TerminalSeats X sel (ticketReady T first) (first).centerAt b)
    (k : ℕ) :
    let writer := readFirstPhysical X gate pad L S
    let start := bootOccurrence X gate pad w template L S
    let born := compileOccurrence start.result
    let retained := ((birthPhysical born).2.raw.flatMap physicalPortWords).length
    start.steps=template.steps+writer.steps+4 ∧
    born.issuance.steps=template.result.issued.steps+
      (template.result.native.steps+4+template.result.physical.steps+template.result.words.steps+4) ∧
    retained=(writer.result.raw.flatMap physicalPortWords).length ∧
    bootWriterFocusBits L.run.result S.made.result writer.result.raw k≤
      (L.run.result.flatMap rootLanePairBits).length+
        (S.made.result.flatMap physicalSeatBits).length+retained := by
  let writer := readFirstPhysical X gate pad L S
  let start := bootOccurrence X gate pad w template L S
  let born := compileOccurrence start.result
  have carried := actual_boot_occurrence_charges_raw_writer_once X gate pad w template L S
  have width : ((birthPhysical born).2.raw.flatMap physicalPortWords).length=
      (writer.result.raw.flatMap physicalPortWords).length :=
    congrArg (fun x : Σ j,PhysicalFile T first j => (x.2.raw.flatMap physicalPortWords).length) carried.1
  refine ⟨carried.2.2.2.1,carried.2.2.2.2,width,?_⟩
  change bootWriterFocusBits L.run.result S.made.result writer.result.raw k≤
      _+((birthPhysical born).2.raw.flatMap physicalPortWords).length
  rw [width]
  exact actual_boot_writer_focus_is_bounded_by_full_returned_tape L.run.result S.made.result k

#print axioms same_first_native_occurrence_has_the_accounted_boot_file
end
end J6R55SelectedPeak
