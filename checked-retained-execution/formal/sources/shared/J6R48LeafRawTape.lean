import J6R21LeafOriginalGate
import J6R21AncestorGather
import J6R21AncestorRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option maxRecDepth 2200

/-! Raw source leaf readers, with no assumed entry value or callback fee.
Wire headers and unary seek lanes are charged by their actual lengths,
including tapes whose local tags subsequently fail validation. -/
namespace J6R48Leaf
open AOracleMachineTime AOracleMachineTimeTape A1R9 A1R10 A1R11 A1R12
open J6R20Ancestor J6R21Ancestor J6R21Leaf J6R19Retained J6R18ChildWrite

def originalDegree {m k : ℕ} : OriginalGateTape m k→ℕ
  | .clause ports _=>ports.length
  | .equal ports=>ports.length
  | .free=>0

theorem raw_bit_address_steps {m k : ℕ} (a : BitAddress m k) (bits : List Bool) :
    (readAddress a bits).steps≤addressFee bits.length k := by
  have h := (seekBlock_exact (fun _=>1) a.code.val bits).2
  have w := sum_map_le_length bits (fun _=>1) 1 (fun _ _=>le_rfl)
  rw [Nat.mul_one] at w
  rw [a.code.property] at h
  unfold readAddress addressFee
  change (seekBlock (fun _=>1) a.code.val bits).steps+a.code.val.length+3≤(10*k+5)*bits.length+k+3
  rw [a.code.property,show (10*k+5)*bits.length=(10*k+4)*bits.length+bits.length by ring]
  omega

theorem raw_original_ports_steps {m k : ℕ} (bits : List Bool) (ports : List (BitAddress m k)) :
    (scanWords bits ports).steps≤1+ports.length*(addressFee bits.length k+2) := by
  induction ports with
  | nil => simp [scanWords]
  | cons a as ih =>
    have h := raw_bit_address_steps a bits
    change (readAddress a bits).steps+(scanWords bits as).steps+2≤
      1+(as.length+1)*(addressFee bits.length k+2)
    rw [Nat.succ_mul as.length]
    omega

theorem raw_original_gate_steps {m k : ℕ} (bits : List Bool) (tape : OriginalGateTape m k) :
    (runOriginalGate bits tape).steps≤originalGateFee bits.length k (originalDegree tape) := by
  cases tape with
  | free => simp [runOriginalGate,originalGateFee,originalDegree]
  | clause ports signs =>
    have h := raw_original_ports_steps bits ports
    unfold runOriginalGate originalGateFee originalDegree
    change (scanWords bits ports).steps+5*ports.length+4≤5+ports.length*(addressFee bits.length k+7)
    rw [Nat.mul_add] at h ⊢
    omega
  | equal ports =>
    have h := raw_original_ports_steps bits ports
    unfold runOriginalGate originalGateFee originalDegree
    change (scanWords bits ports).steps+5*ports.length+4≤5+ports.length*(addressFee bits.length k+7)
    rw [Nat.mul_add] at h ⊢
    omega

theorem raw_uv_gate_steps {m k p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hℓ : 0<ell) (bits : List Bool) (tape : OriginalGateTape m k) :
    (uvGate hp he hℓ tape bits).steps≤
      originalGateFee bits.length k (originalDegree tape)+uvWidth fw.length ell p+4 :=
  Nat.add_le_add_right (Nat.add_le_add_right (raw_original_gate_steps bits tape) _) _

def wireCharge (width : ℕ) (wire : WireRead) : ℕ :=
  3*wire.header.length+4*wire.lane.length+width+12

def rawWireFee (width : ℕ) (wires : List WireRead) : ℕ :=
  (wires.map (wireCharge width)).sum

theorem raw_wire_gather_steps (w : ℕ) (wires : List WireRead) (bits : List Bool) :
    (gather w wires bits).result.length=wires.length ∧
      (gather w wires bits).steps≤rawWireFee w wires := by
  induction wires with
  | nil => simp [gather,A1R12.mapMeter,rawWireFee]
  | cons u us ih =>
    have h := (attachBit_exact bits u).2
    rcases ih with ⟨hlen,hcost⟩
    constructor
    · change (List.cons (attachBit bits u).result (gather w us bits).result).length=_
      simp only [List.length_cons,hlen]
    · change (attachBit bits u).steps+(gather w us bits).steps+(w+1)+4≤
        wireCharge w u+rawWireFee w us
      unfold wireCharge
      omega

theorem raw_port_parse_steps (a : ℕ) (x : Raw) :
    (readPort a x).steps≤portFee a := by
  fun_cases readPort a x with
  | case1 s bits b =>
    change (J6R19Retained.scanWidth a bits).steps+8≤_
    rw [(J6R19Retained.scanWidth_exact a bits).2,portFee]
  | case2 xs h =>
    simp only [portFee]
    omega

theorem raw_tape_parse_caps (a : ℕ) (raw : List Raw) :
    (readTape a raw).result.length≤raw.length ∧ (readTape a raw).steps≤tapeFee a raw.length := by
  induction raw with
  | nil => simp [readTape,tapeFee]
  | cons x xs ih =>
    have h := raw_port_parse_steps a x
    rcases ih with ⟨n,c⟩
    constructor
    · simp only [readTape,List.length_cons]
      cases e : (readPort a x).result
      · exact n.trans (Nat.le_succ _)
      · exact Nat.succ_le_succ n
    · change (readPort a x).steps+(readTape a xs).steps+a+8≤tapeFee a (xs.length+1)
      unfold tapeFee at c ⊢
      rw [Nat.succ_mul xs.length]
      omega

theorem raw_fill_slots_caps {a : ℕ} (side : Bool) (tape : List (Key a×Bool))
    (slots : List (J6R15ModeCost.Word a)) :
    (fillSlots side tape slots).result.length=slots.length ∧
      (fillSlots side tape slots).steps≤slotFee a tape.length slots.length := by
  let go (w : J6R15ModeCost.Word a) : Meter (SlotBit a) :=
    let z := findBit ⟨side,w⟩ tape
    ⟨⟨w,z.result⟩,z.steps⟩
  obtain ⟨e,c⟩ := A1R12.mapMeter_exact go (a+1) (findFee a tape.length) slots
    (fun w _=> findBit_cost ⟨side,w⟩ tape)
  constructor
  · change (A1R12.mapMeter go (a+1) slots).result.length=_
    rw [e,List.length_map]
  · change (A1R12.mapMeter go (a+1) slots).steps≤_
    exact c.trans (Nat.mul_le_mul_left _ (by omega))

theorem raw_slot_fee_mono (a r : ℕ) {n N : ℕ} (hn : n≤N) :
    slotFee a n r≤slotFee a N r := by
  unfold slotFee findFee
  gcongr

theorem raw_route_caps {a : ℕ} (d : ℕ) (rs cs : List (J6R15ModeCost.Word a)) (raw : List Raw) :
    (routeTrace d rs cs raw).result.1.length=rs.length ∧
    (routeTrace d rs cs raw).result.2.length=cs.length ∧
    (routeTrace d rs cs raw).steps≤traceRouteFee a d raw.length rs.length cs.length := by
  let n := normalizeTape a d raw
  let z := readTape a n.result
  let r := fillSlots false z.result rs
  let c := fillSlots true z.result cs
  have h := normalizeTape_exact a d raw
  have len : n.result.length=raw.length := by
    change (normalizeTape a d raw).result.length=_
    rw [h.1,List.length_map]
  obtain ⟨nz,zt⟩ := raw_tape_parse_caps a n.result
  have nz' : z.result.length≤raw.length := nz.trans_eq len
  obtain ⟨rh,rt⟩ := raw_fill_slots_caps false z.result rs
  obtain ⟨ch,ct⟩ := raw_fill_slots_caps true z.result cs
  change r.result.length=_ ∧ c.result.length=_ ∧ _
  refine ⟨rh,ch,?_⟩
  have nr := h.2
  change n.steps≤_ at nr
  change z.steps≤tapeFee a n.result.length at zt
  rw [len] at zt
  have rb := rt.trans (raw_slot_fee_mono a rs.length nz')
  have cb := ct.trans (raw_slot_fee_mono a cs.length nz')
  change r.steps≤_ at rb
  change c.steps≤_ at cb
  change n.steps+(z.steps+r.steps+c.steps+4)+4≤_
  unfold traceRouteFee routeFee
  omega

#print axioms raw_bit_address_steps
#print axioms raw_original_gate_steps
#print axioms raw_uv_gate_steps
#print axioms raw_wire_gather_steps
#print axioms raw_tape_parse_caps
#print axioms raw_route_caps
end J6R48Leaf
