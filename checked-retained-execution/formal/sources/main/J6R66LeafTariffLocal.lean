import J6R65LeafRateEntry
import J6R66LeafTariffNative

/-! Preserve the finer original per-entry exponent. The leaf-level
`2^(6H)` corollary is coarser: before taking that maximum, a real
published mesh of side `L` incurs `2^(6 L log₂ s)` in this meter. -/
namespace J6R66LeafTariff
open scoped Polynomial
open J6R18ChildWrite J6R21Ancestor J6R48Leaf J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R65LeafRate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Record" => (Stored key prec tw bw (PagedEnvelope f ell prec page))

theorem actual_reader_rate_in_its_own_mesh
    (B : Bank) (r : Record) (d : pageFields r)
    (creator : J6R15ModeCost.Word key) (selector : J6R15ModeCost.Word page)
    (outer : (locate creator B.records).result=some r)
    (inner : (locate selector r.payload.pages).result=some d)
    (rows : d.rows.length≤2^r.payload.shape.a)
    (e p edges dep : ℕ) (wires : List WireRead) :
    rawPageFee e p edges B (.generated creator selector dep wires)≤
      (d.modes.length+2)^(2^r.payload.shape.a)*actualPacketPrefactor B r d p dep wires := by
  let S := r.payload.shape
  let h := (d.modes.length+2)^(2^S.a)
  let nonpacket := readerNonPacket B r d p dep wires
  let packet := packetFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
    d.rows.length d.cols.length d.modes.length S.pPos
  let term := packetNonTreeFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
    d.rows.length d.cols.length d.modes.length S.pPos
  let tree := packetTreeScale S.old.length ell S.p d.modes.length d.rows.length r.context.codeWidth.val S.w S.pPos
  let frame := packetFramingFee S.old.length ell S.p S.w
  have pp : packet+frame≤h*(term+tree+frame) :=
    packetFee_geometric S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
      d.rows.length d.cols.length d.modes.length S.pPos rows
  have non : nonpacket≤h*nonpacket := Nat.le_mul_of_pos_left _ (by dsimp only [h]; positivity)
  rw [found_generated_read_has_actual_tariff B r d creator selector outer inner e p edges dep wires]
  change nonpacket+packet≤h*(nonpacket+term+tree+frame)
  calc
    _≤h*nonpacket+h*(term+tree+frame) :=
      Nat.add_le_add non ((Nat.le_add_right packet frame).trans pp)
    _=_ := by ring

theorem actual_reader_L_log_bound
    (B : Bank) (r : Record) (d : pageFields r)
    (creator : J6R15ModeCost.Word key) (selector : J6R15ModeCost.Word page)
    (outer : (locate creator B.records).result=some r)
    (inner : (locate selector r.payload.pages).result=some d)
    (s : ℕ) (rows : d.rows.length≤2^r.payload.shape.a)
    (modes : d.modes.length+2≤2^(6*Nat.clog 2 s))
    (e p edges dep : ℕ) (wires : List WireRead) :
    rawPageFee e p edges B (.generated creator selector dep wires)≤
      2^(6*Nat.clog 2 s*(2^r.payload.shape.a))*actualPacketPrefactor B r d p dep wires := by
  have geom := actual_reader_rate_in_its_own_mesh B r d creator selector outer inner rows e p edges dep wires
  refine geom.trans (Nat.mul_le_mul_right _ ?_)
  exact (Nat.pow_le_pow_left modes _).trans_eq (pow_mul _ _ _).symm

#print axioms actual_reader_rate_in_its_own_mesh
#print axioms actual_reader_L_log_bound
end J6R66LeafTariff
