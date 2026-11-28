import J6R62LeafReader

/-! Price the extant root packet command without any callback-fee input.
A root packet uses a depth-zero body, a unary address on the shared
clock, and the existing parsed resident fields, whose sizes determine
the combinatorial, route, and arithmetic bounds. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost
open J6R18ChildWrite J6R20Ancestor J6R21Ancestor J6R21Leaf J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage
open J6R48Leaf J6R50Leaf J6R62Leaf

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 9500000

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Rec" => (Stored key prec tw bw (PagedEnvelope f ell prec page))

def stoppedPacketLookupCap (B : Bank) (r : Rec) (field : pageFields r) (p E U : ℕ) : ℕ :=
  let S := r.payload.shape
  locateFee key B.records.length+locateFee page r.payload.pages.length+
    E*(3*U+4*E+(S.a+2)+12)+
    invokeFee S.a S.old.length ell S.p p S.i.val S.w r.context.codeWidth.val 0 E
      field.rows.length field.cols.length field.modes.length S.pPos+
    invokeStampFee key prec tw bw+14

theorem root_packet_wire_bound (E U a : ℕ) (wires : List WireRead)
    (count : wires.length≤ E) (fit : ∀ w∈wires,w.header.length≤ U ∧ w.lane.length≤ E) :
    rawWireFee (a+2) wires≤ E*(3*U+4*E+(a+2)+12) := by
  unfold rawWireFee
  exact (sum_map_cap wires (wireCharge (a+2)) _ (fun w hw=>by
    have l := fit w hw
    unfold wireCharge
    omega)).trans (Nat.mul_le_mul_right _ count)

theorem root_packet_invocation_monotone_wire_count (a e ell p q i w b r c m : ℕ) (hp : 0<p)
    {u v : ℕ} (h : u≤ v) :
    invokeFee a e ell p q i w b 0 u r c m hp≤ invokeFee a e ell p q i w b 0 v r c m hp := by
  unfold invokeFee traceRouteFee normalizeFee routeFee J6R20Ancestor.tapeFee slotFee findFee
  gcongr

theorem literal_found_root_packet_price
    (B : Bank) (r : Rec) (field : pageFields r)
    (creator : Word key) (selector : Word page)
    (outer : (locate creator B.records).result=some r)
    (inner : (locate selector r.payload.pages).result=some field)
    (wires : List WireRead) (p e E U : ℕ)
    (count : wires.length≤ E) (fit : ∀ w∈wires,w.header.length≤ U ∧ w.lane.length≤ E) :
    readCmdFee B e p E (.packet creator selector 0 wires)≤ stoppedPacketLookupCap B r field p E U := by
  dsimp only [readCmdFee,rawPageFee]
  rw [outer]
  dsimp only
  rw [inner]
  dsimp only [stoppedPacketLookupCap]
  have i := root_packet_invocation_monotone_wire_count r.payload.shape.a
    r.payload.shape.old.length ell r.payload.shape.p p r.payload.shape.i.val
    r.payload.shape.w r.context.codeWidth.val field.rows.length field.cols.length
    field.modes.length r.payload.shape.pPos count
  have c := root_packet_wire_bound E U r.payload.shape.a wires count fit
  simp only [Nat.zero_add]
  omega

#print axioms root_packet_wire_bound
#print axioms root_packet_invocation_monotone_wire_count
#print axioms literal_found_root_packet_price
end J6R68CanonicalRootWriter
