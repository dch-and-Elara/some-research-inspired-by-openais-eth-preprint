import J6R65LeafRateNumerics
import J6R48LeafRawReader
import J6R57LeafCapPacket

/-! One genuine resident entry's exact tariff. The outer/inner banks,
ancestral route, stamp, and resize are exposed separately from the
packet enumeration. Its dimensions are facts about the found record,
not an oracle-time premise for the whole leaf. -/
namespace J6R65LeafRate
open scoped Polynomial
open AOracleMachineTime A1R12 J6R21Ancestor J6R27OriginalGate
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48Leaf
open J6R20Ancestor J6R18ChildWrite J6R19Retained J6R57LeafCap J1PPrinted

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 22000000
set_option maxRecDepth 3400

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Rec" => (Stored key prec tw bw (PagedEnvelope f ell prec page))

def readerNonPacket (B : Bank) (r : Rec) (d : pageFields r)
    (p dep : ℕ) (wires : List WireRead) : ℕ :=
  let S := r.payload.shape
  locateFee key B.records.length+locateFee page r.payload.pages.length+
    rawWireFee (dep+S.a+2) wires+
    traceRouteFee S.a dep wires.length d.rows.length d.cols.length+
    boxFee S.old.length ell S.p p+invokeStampFee key prec tw bw+18

theorem found_generated_read_has_actual_tariff
    (B : Bank) (r : Rec) (d : pageFields r)
    (creator : J6R15ModeCost.Word key) (selector : J6R15ModeCost.Word page)
    (outer : (locate creator B.records).result=some r)
    (inner : (locate selector r.payload.pages).result=some d)
    (e p edges dep : ℕ) (wires : List WireRead) :
    let S := r.payload.shape
    rawPageFee e p edges B (.generated creator selector dep wires)=
      readerNonPacket B r d p dep wires+
        packetFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
          d.rows.length d.cols.length d.modes.length S.pPos := by
  dsimp only [rawPageFee]
  rw [outer]
  dsimp only
  rw [inner]
  dsimp only [invokeFee,readerNonPacket]
  ring

def actualPacketPrefactor (B : Bank) (r : Rec) (d : pageFields r)
    (p dep : ℕ) (wires : List WireRead) : ℕ :=
  let S := r.payload.shape
  readerNonPacket B r d p dep wires+
    packetNonTreeFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
      d.rows.length d.cols.length d.modes.length S.pPos+
    packetTreeScale S.old.length ell S.p d.modes.length d.rows.length r.context.codeWidth.val S.w S.pPos+
    packetFramingFee S.old.length ell S.p S.w

theorem found_generated_reader_rate_from_created_page_dimensions
    (B : Bank) (r : Rec) (d : pageFields r)
    (creator : J6R15ModeCost.Word key) (selector : J6R15ModeCost.Word page)
    (outer : (locate creator B.records).result=some r)
    (inner : (locate selector r.payload.pages).result=some d)
    (s createdAt : ℕ) (large : 1024≤Nat.clog 2 s)
    (axis : r.payload.shape.a=stepA (Nat.clog 2 s) createdAt)
    (rows : d.rows.length≤2^r.payload.shape.a)
    (modes : d.modes.length+2≤2^(6*Nat.clog 2 s))
    (e p edges dep : ℕ) (wires : List WireRead) :
    rawPageFee e p edges B (.generated creator selector dep wires)≤
      2^(6*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))*actualPacketPrefactor B r d p dep wires := by
  let S := r.payload.shape
  let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
  let x := readerNonPacket B r d p dep wires
  let w := 2^(6*H)
  let entry := packetFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
    d.rows.length d.cols.length d.modes.length S.pPos
  let ff := packetFramingFee S.old.length ell S.p S.w
  let linear := packetNonTreeFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
    d.rows.length d.cols.length d.modes.length S.pPos
  let tm := packetTreeScale S.old.length ell S.p d.modes.length d.rows.length r.context.codeWidth.val S.w S.pPos
  have shape : d.rows.length≤2^stepA (Nat.clog 2 s) createdAt := axis ▸ rows
  have g := actual_printed_packet_entry_geometric s createdAt S.old.length ell S.p S.i.val S.w
    r.context.codeWidth.val d.rows.length d.cols.length d.modes.length 6 S.pPos large shape modes
  have transport (a : ℕ) (index : a=stepA (Nat.clog 2 s) createdAt) :
      packetFee a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
          d.rows.length d.cols.length d.modes.length S.pPos+ff≤
        w*(packetNonTreeFee a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
          d.rows.length d.cols.length d.modes.length S.pPos+tm+ff) := by
    rw [index]
    exact g
  have gg : entry+ff≤w*(linear+tm+ff) := transport S.a axis
  have v : x≤w*x := Nat.le_mul_of_pos_left _ (by positivity)
  rw [found_generated_read_has_actual_tariff B r d creator selector outer inner e p edges dep wires]
  change x+entry≤w*(x+linear+tm+ff)
  calc
    _≤w*x+w*(linear+tm+ff) := Nat.add_le_add v ((Nat.le_add_right entry ff).trans gg)
    _=_ := by ring

#print axioms found_generated_read_has_actual_tariff
#print axioms found_generated_reader_rate_from_created_page_dimensions
end J6R65LeafRate
