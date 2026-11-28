import J6R55BootBodiesBits
import J6R54PeakInputOccurrence
import J6R54PeakInputReserve
import J6R52PeakCache

/-! Selected fields at the original lane/seat-to-port writer. The
inputs are the actual paired lane rows and actual seat tape; the
output prefix contains the exactly paid two half-port copies, not
a re-created row or a newly enumerated physical order. -/
namespace J6R55SelectedPeak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R37StructuredRoot J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R48RawRoute J6R27OriginalGate J6R36ChildFramedRoute J6R26DescriptorTree
open J6R55BootBodies J6R54PeakInput J6R52Peak

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 15500000

variable {m key prec pad a b : ℕ}
local notation "LaneRow" => RootLanes m key prec pad
local notation "S" => SeatField a b
local notation "Port" => PortRow (rootHalfWidth m+1)

def copiedBootPair (lanes : LaneRow) (seat : S) : Meter (List Port) :=
  let r := writeNextPort false seat.rowGroup lanes.gate
  let c := writeNextPort true seat.colGroup lanes.packet
  ⟨[r.result,c.result],r.steps+c.steps⟩

def resumeBootPairCopies (heads : List (Meter (List Port)))
    (last : Meter (Option (List Port))) : Meter (Option (List Port)) :=
  heads.foldr (fun h t=>⟨t.result.map (h.result++·),h.steps+t.steps+3*a+3*b+8⟩) last

theorem boot_writer_resumes_after_its_actual_paid_pairs
    (pre : List (LaneRow×S)) (afterLane : List LaneRow) (afterSeat : List S) :
    writeBootRows (pre.map Prod.fst++afterLane) (pre.map Prod.snd++afterSeat)=
      resumeBootPairCopies (a:=a) (b:=b) (pre.map (fun h=>copiedBootPair h.1 h.2))
        (writeBootRows afterLane afterSeat) := by
  induction pre with
  | nil => rfl
  | cons h hs ih =>
    simp only [List.map_cons,List.cons_append,writeBootRows,resumeBootPairCopies,List.foldr_cons,
      copiedBootPair,List.nil_append] at *
    rw [ih]

def rootLanePairBits (x : LaneRow) : List Bool :=
  laneBits x.gate++laneBits x.packet

def physicalSeatBits {a b : ℕ} (s : SeatField a b) : List Bool :=
  s.page.bits++s.slot.bits++s.rowGroup.bits++s.colGroup.bits

theorem physical_seat_bits_exact {a b : ℕ} (s : SeatField a b) :
    (physicalSeatBits s).length=b+a+12 := by
  simp only [physicalSeatBits,List.length_append,s.page.size,s.slot.size,s.rowGroup.size,s.colGroup.size]

theorem boot_pair_output_bits_exact (lanes : LaneRow) (seat : S) :
    ((copiedBootPair lanes seat).result.flatMap physicalPortWords).length=
      2*(rootHalfWidth m+1+6)+lanes.gate.body.length+lanes.packet.body.length := by
  simp only [copiedBootPair,actual_next_port_exact,List.flatMap_cons,List.flatMap_nil,
    List.length_append,List.length_nil,physical_port_words_exact,nextPortView]
  omega

def bootWriterFocusBits (lanes : List LaneRow) (seats : List S)
    (written : List Port) (n : ℕ) : ℕ :=
  (lanes.flatMap rootLanePairBits).length+(seats.flatMap physicalSeatBits).length+
    ((written.take n).flatMap physicalPortWords).length

theorem actual_boot_writer_focus_is_bounded_by_full_returned_tape
    (lanes : List LaneRow) (seats : List S) (n : ℕ) :
    let done := writeBootRows lanes seats
    let written := done.result.getD []
    bootWriterFocusBits lanes seats written n≤
      (lanes.flatMap rootLanePairBits).length+(seats.flatMap physicalSeatBits).length+
        (written.flatMap physicalPortWords).length := by
  dsimp only [bootWriterFocusBits]
  exact Nat.add_le_add_left (encoded_take_le_full ((writeBootRows lanes seats).result.getD [])
    physicalPortWords n) _

#print axioms boot_writer_resumes_after_its_actual_paid_pairs
#print axioms physical_seat_bits_exact
#print axioms boot_pair_output_bits_exact
#print axioms actual_boot_writer_focus_is_bounded_by_full_returned_tape
end J6R55SelectedPeak
