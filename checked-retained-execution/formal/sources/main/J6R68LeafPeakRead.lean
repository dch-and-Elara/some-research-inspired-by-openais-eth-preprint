import J6R68LeafPeakClock
import J6R62LeafReader

/-! The real positive terminal uses a *right-nested* product of
literal row reads. A strict execution can retain all earlier row
values while reading the next row. Count them, together with the
actual held Boolean sibling sums and source command fields. -/
namespace J6R68.LeafPeak
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R15ModeCost J6R21Leaf J6R21Ancestor J6R27OriginalGate
open J6R22Active J6R24MeteredRecursion J6R33StatefulArithmeticPage
open J6R48Leaf J6R50Leaf J6R62Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6200000
set_option Elab.async false

def leafCommandFields {key page : ℕ} : ReadCmd key page → List Bool
  | .gate _ .free => []
  | .gate _ (.equal keys) => keys.flatMap J6R15ModeCost.Word.bits
  | .gate _ (.clause keys signs) => keys.flatMap J6R15ModeCost.Word.bits++signs
  | .packet k pg _ wires => k.bits++pg.bits++wires.flatMap (fun wire=>wire.header++wire.lane)

theorem packet_command_counts_its_exact_source_fields {key page : ℕ}
    (k : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) :
    (leafCommandFields (.packet k pg depth wires)).length=
      key+page+((wires.map (fun wire=>wire.header.length+wire.lane.length)).sum) := by
  have wireLen :
      (wires.flatMap (fun (wire : WireRead)=>wire.header++wire.lane)).length=
        (wires.map (fun wire=>wire.header.length+wire.lane.length)).sum := by
    induction wires with
    | nil => rfl
    | cons w ws ih =>
      simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,ih]
  simp only [leafCommandFields,List.length_append,k.size,pg.size,wireLen]

variable {f : ℤ[X]} {p ell key prec tw bw page : ℕ}

def actualRowQuery (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (rows : List (ReadCmd key page)) :
    List Bool→Meter (Block F ell) :=
  readProduct F.hp F.sizePos pos rows (fun r=>r.read hf F pos B)

/-- The proof continuation is not a second evaluation or a stored
tuple list. It reads off the exact waiting operands of the literal
right-nested fold at this command. -/
theorem read_product_has_that_exact_pending_context
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (pre post : List (ReadCmd key page)) (cmd : ReadCmd key page) (bits : List Bool) :
    let waiting := pre.map (fun x=>x.read hf F pos B bits)
    let now := cmd.read hf F pos B bits
    let suffix := actualRowQuery hf F pos B post bits
    actualRowQuery hf F pos B (pre++cmd::post) bits=
      waiting.foldr (mulM F.hp) (mulM F.hp now suffix) := by
  induction pre with
  | nil => rfl
  | cons x xs ih =>
    change mulM F.hp (x.read hf F pos B bits) (actualRowQuery hf F pos B (xs++cmd::post) bits)=
      mulM F.hp (x.read hf F pos B bits) _
    rw [ih]

/-- At a positive terminal Boolean leaf, the current read is from
the literal command list and has its attached page/gate format in
the same bank. The footprint includes both kinds of suspended
blocks and the current read's returned operand, but *not* scratch
inside the gate or generated packet evaluator. -/
theorem same_assignment_and_current_entry_fit_named_leaf_registers
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clock : List Unit) (rows pre post : List (ReadCmd key page))
    (cmd : ReadCmd key page) (order : rows=pre++cmd::post)
    (formats : ∀ t∈rows,ReadFormat B clock.length t)
    (rev : List Bool) (lefts : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B rows) clock [] rev lefts) :
    let bits := (reverseTape rev []).result
    let pending := pre.map (fun r=>(r.read hf F pos B bits).result)
    let current := cmd.read hf F pos B bits
    bits.length=clock.length ∧ ReadFormat B clock.length cmd ∧
    (lefts.flatMap leafPayload).length+rev.length+bits.length+
      (pending.flatMap leafPayload).length+(leafPayload current.result).length+
        (leafCommandFields cmd).length≤
      (clock.length+rows.length)*(ell*(F.words.length*p))+2*clock.length+
        (leafCommandFields cmd).length := by
  let bits := (reverseTape rev []).result
  let pending := pre.map (fun r=>(r.read hf F pos B bits).result)
  have cutdata := actual_clock_stop_has_one_forward_tape cut
  have inList : cmd∈rows := by
    rw [order]
    exact List.mem_append_right _ List.mem_cons_self
  have fact : pre.length+1≤rows.length := by
    rw [order,List.length_append,List.length_cons]
    omega
  have rowSpace :
      (pending.flatMap leafPayload).length+(leafPayload (cmd.read hf F pos B bits).result).length≤
        rows.length*(ell*(F.words.length*p)) := by
    rw [encoded_blocks_width,List.length_map,leaf_payload_width,←Nat.succ_mul]
    exact Nat.mul_le_mul_right _ fact
  refine ⟨cutdata.1,formats cmd inList,?_⟩
  have sum := Nat.add_le_add_right (Nat.add_le_add cutdata.2.2 rowSpace) (leafCommandFields cmd).length
  calc
    _ ≤ (clock.length*(ell*(F.words.length*p))+2*clock.length)+
        rows.length*(ell*(F.words.length*p))+(leafCommandFields cmd).length := by
      simpa only [Nat.add_assoc] using sum
    _ = _ := by ring

/-- At that command's generated-page branch, the format provides the
actual addressed occurrence and actual page obtained by the two
lookups, rather than a freely provided payload with the same value. -/
theorem formatted_packet_uses_the_same_live_page
    (B : PageBank f ell key prec tw bw page) (N : ℕ)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (dep : ℕ) (wires : List WireRead)
    (fit : ReadFormat B N (.packet id pg dep wires)) :
    ∃ r,(locate id B.records).result=some r ∧ id=r.stamp.creator ∧
      r.payload.shape.birth=r.stamp.created ∧
      ∃ d,(locate pg r.payload.pages).result=some d ∧ PacketForm r d := fit

#print axioms packet_command_counts_its_exact_source_fields
#print axioms read_product_has_that_exact_pending_context
#print axioms same_assignment_and_current_entry_fit_named_leaf_registers
#print axioms formatted_packet_uses_the_same_live_page
end J6R68.LeafPeak