import J6R68LeafPeakPacketEngine
import J6R68LeafPeakMaximum

/-! The generated-Page command invokes a literal internal producer,
not the external entry routine allowed for the initial tensor input.
These projections identify the actual selected Page, one raw read,
creation-frame row coefficient and source product, and the resize.
They are not another issued query or a copy of the resident file. -/
namespace J6R68.LeafPeak.Packet
open scoped Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10 A1R12
open J6R18ChildWrite J6R19Retained J6R20Ancestor J6R21Ancestor J6R21Leaf
open J6R22Active J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R48Leaf J6R50Leaf J6R62Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3200
set_option Elab.async false

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
abbrev PacketRecord (f : ℤ[X]) (ell key prec tw bw page : ℕ) :=
  Stored key prec tw bw (PagedEnvelope f ell prec page)

structure LivePageHit (B : PageBank f ell key prec tw bw page)
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) where
  record : PacketRecord f ell key prec tw bw page
  hit : (locate id B.records).result=some record
  own : id=record.stamp.creator
  born : record.payload.shape.birth=record.stamp.created
  data : pageFields record
  pageHit : (locate pg record.payload.pages).result=some data
  valid : PacketForm record data

theorem exists_live_page_for_actual_command (B : PageBank f ell key prec tw bw page)
    (N : ℕ) (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ)
    (wires : List WireRead) (form : ReadFormat B N (.packet id pg d wires)) :
    Nonempty (LivePageHit B id pg) := by
  obtain ⟨R,hit,own,born,data,here,form⟩ := formatted_packet_uses_the_same_live_page B N id pg d wires form
  exact ⟨⟨R,hit,own,born,data,here,form⟩⟩

namespace LivePageHit
variable {B : PageBank f ell key prec tw bw page}
variable {id : J6R15ModeCost.Word key} {pg : J6R15ModeCost.Word page}
variable (Q : LivePageHit B id pg)

abbrev S := Q.record.payload.shape
abbrev codeWidth := Q.record.context.codeWidth.val
abbrev center := Q.record.context.center
def W : ℕ := ell*(Q.S.old.length*Q.S.p)

theorem mode_codes_width :
    ∀ m∈Q.data.modes,m.code.length=Q.codeWidth := by
  intro m h
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp h
  exact (congrArg List.length (Q.valid.modeCodes j)).trans (encodeBits_length _ _)

def gathered (d : ℕ) (wires : List WireRead) (bits : List Bool) : Meter (List Raw) :=
  gather (d+Q.S.a+2) wires bits

def routed (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (List (SlotBit Q.S.a)×List (SlotBit Q.S.a)) :=
  routeTrace d Q.data.rows Q.data.cols (Q.gathered d wires bits).result

def board (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (List (List (Term Q.S.old ell))) :=
  let R := (Q.routed d wires bits).result
  packRows Q.S.pPos Q.S.degreePos pos Q.data.probe Q.center Q.S.i Q.codeWidth R.1 R.2 Q.data.modes

def tests : Meter (List (List Bool×List Bool)) := prepareChecks Q.codeWidth Q.data.modes

def coefficient (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (UVBlock Q.S.old ell) :=
  evalRows Q.S.pPos Q.codeWidth Q.S.w Q.tests.result (Q.board pos d wires bits).result []
    (oneM Q.S.pPos Q.S.degreePos pos).result

def moments (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (UVBlock Q.S.old ell) :=
  sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i (Q.routed d wires bits).result.2 Q.data.modes

def createdValue (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (UVBlock Q.S.old ell) :=
  let R := (Q.routed d wires bits).result
  packetResult Q.S.pPos Q.S.degreePos pos Q.data.probe Q.center Q.S.i Q.codeWidth R.1 R.2 Q.data.modes

theorem creation_uses_exact_coefficient_and_moments
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    let a := Q.coefficient pos d wires bits
    let b := Q.moments pos d wires bits
    let c := uvMul Q.S.pPos a.result b.result
    (Q.createdValue pos d wires bits).result=c.result ∧
    (Q.createdValue pos d wires bits).steps=(Q.board pos d wires bits).steps+Q.tests.steps+
      (oneM Q.S.pPos Q.S.degreePos pos).steps+a.steps+b.steps+c.steps+12 := ⟨rfl,rfl⟩

def delivered {p : ℕ} (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (d : ℕ) (wires : List WireRead) (bits : List Bool) : Meter (Block F ell) :=
  resizeUV (shapeCompatible Q.S hf F.hp F.exactMod) (Q.createdValue pos d wires bits).result

theorem actual_read_returns_this_creation_value_and_charges_it_once
    {p : ℕ} (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    (.packet id pg d wires : ReadCmd key page).read hf F pos B bits=
      ⟨(Q.delivered hf F pos d wires bits).result,
        (locate id B.records).steps+(locate pg Q.record.payload.pages).steps+
        (Q.gathered d wires bits).steps+(Q.routed d wires bits).steps+
        (Q.createdValue pos d wires bits).steps+(Q.delivered hf F pos d wires bits).steps+
        invokeStampFee key prec tw bw+18⟩ ∧ Q.record.stamp.created.val=Q.S.p := by
  obtain ⟨hit,tag⟩ := consumes_exact_page hf F pos id pg d wires bits B Q.record Q.hit Q.data Q.pageHit
    Q.own Q.born
  refine ⟨?_,tag⟩
  change requireWord F.hp (consumePage hf F pos id pg d wires bits B)=_
  rw [hit,requireWord]
  try dsimp only
  have arith :
      (invokeTrace Q.S.pPos Q.S.degreePos pos (shapeCompatible Q.S hf F.hp F.exactMod)
        Q.data.probe Q.center Q.S.i Q.codeWidth d Q.data.rows Q.data.cols Q.data.modes
        (Q.gathered d wires bits).result).steps=
      (Q.routed d wires bits).steps+(Q.createdValue pos d wires bits).steps+
        (Q.delivered hf F pos d wires bits).steps+4 := rfl
  congr 1
  change (locate id B.records).steps+(locate pg Q.record.payload.pages).steps+
      (Q.gathered d wires bits).steps+
      (invokeTrace Q.S.pPos Q.S.degreePos pos (shapeCompatible Q.S hf F.hp F.exactMod)
        Q.data.probe Q.center Q.S.i Q.codeWidth d Q.data.rows Q.data.cols Q.data.modes
        (Q.gathered d wires bits).result).steps+
      invokeStampFee key prec tw bw+12+2=_
  rw [arith]
  omega

#print axioms mode_codes_width
#print axioms creation_uses_exact_coefficient_and_moments
#print axioms actual_read_returns_this_creation_value_and_charges_it_once
end LivePageHit

#print axioms exists_live_page_for_actual_command
end J6R68.LeafPeak.Packet


/-! Exact stage sizes for the same fetched, original creation-time
packet entry. Choose cuts of that entry, not of a witness enumerator
on a different table. The safe named setup sum counts every source
routing buffer as a separate copy even where immutable prefix sharing
can reduce it. -/
namespace J6R68.LeafPeak.Packet
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R18ChildWrite J6R19Retained
open J6R20Ancestor J6R21Ancestor J6R21Leaf J6R22Active J6R24MeteredRecursion
open J6R33StatefulArithmeticPage J6R48Leaf J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 3300
set_option Elab.async false

namespace LivePageHit

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
variable {B : PageBank f ell key prec tw bw page}
variable {id : J6R15ModeCost.Word key} {pg : J6R15ModeCost.Word page}
variable (Q : LivePageHit B id pg)

def routeRoom (wires : List WireRead) : ℕ :=
  2*gatheredWidth wires+wires.length*(Q.S.a+3)+(Q.data.rows.length+Q.data.cols.length)*(Q.S.a+1)

def routeBits (d : ℕ) (wires : List WireRead) (bits : List Bool) : ℕ :=
  let raw := (Q.gathered d wires bits).result
  let normalized := (normalizeTape Q.S.a d raw).result
  let parsed := (readTape Q.S.a normalized).result
  let r := (Q.routed d wires bits).result
  (rawBits raw).length+(rawBits normalized).length+(parsed.flatMap parsedWords).length+
    (r.1.flatMap slotBitWords).length+(r.2.flatMap slotBitWords).length

def tableRoom : ℕ :=
  Q.data.rows.length*((Q.data.modes.length+1)*(Q.codeWidth+Q.W))+
    Q.data.modes.length*(Q.codeWidth+Q.S.w)

def tableSize (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) : ℕ :=
  (tableBits (Q.board pos d wires bits).result).length+(Q.tests.result.flatMap checkBits).length

def choiceRoom : ℕ :=
  choiceBudget Q.data.rows.length (Q.data.modes.length+1) Q.codeWidth Q.W

theorem exact_routing_fits_generated_page
    (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    let R := (Q.routed d wires bits).result
    R.1.length=Q.data.rows.length ∧ R.2.length=Q.data.cols.length ∧
      Q.routeBits d wires bits≤Q.routeRoom wires := by
  have ea := actual_gather_result_width (d+Q.S.a+2) wires bits
  have aa := actual_route_named_tapes d Q.data.rows Q.data.cols (Q.gathered d wires bits).result
  refine ⟨aa.1,aa.2.1,?_⟩
  have a := aa.2.2
  change Q.routeBits d wires bits≤
    2*(rawBits (Q.gathered d wires bits).result).length+
      (Q.gathered d wires bits).result.length*(Q.S.a+3)+
        (Q.data.rows.length+Q.data.cols.length)*(Q.S.a+1) at a
  have g := ea.1
  have w := ea.2
  change (Q.gathered d wires bits).result.length=wires.length at g
  change (rawBits (Q.gathered d wires bits).result).length=gatheredWidth wires at w
  rw [g,w] at a
  exact a

theorem exact_affine_and_test_tables_for_this_page
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) :
    let T := (Q.board pos d wires bits).result
    T.length=Q.data.rows.length ∧
    (∀ row∈T,row.length≤Q.data.modes.length+1 ∧ ∀ t∈row,t.code.length=Q.codeWidth) ∧
    Q.tableSize pos d wires bits=Q.tableRoom := by
  let R := (Q.routed d wires bits).result
  let T := (Q.board pos d wires bits).result
  obtain ⟨row,rwidth,sz⟩ := actual_packet_has_only_its_affine_table Q.S.pPos Q.S.degreePos pos
    Q.data.probe Q.center Q.S.i Q.codeWidth R.1 R.2 Q.data.modes Q.mode_codes_width
  have lens := (Q.exact_routing_fits_generated_page d wires bits).1
  obtain ⟨_,_,modes⟩ := actual_packet_has_only_its_mode_tests Q.codeWidth Q.data.modes Q.mode_codes_width
  change T.length=R.1.length at row
  change (tableBits T).length=R.1.length*((Q.data.modes.length+1)*(Q.codeWidth+Q.W)) at sz
  change (Q.tests.result.flatMap checkBits).length=_ at modes
  refine ⟨row.trans lens,(fun r hr=>⟨(rwidth r hr).1.le,(rwidth r hr).2⟩),?_⟩
  unfold tableSize tableRoom
  rw [sz,modes,lens]

theorem true_entry_setup_named_payload
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool) (j k : ℕ) :
    Q.routeBits d wires bits+
      (tableBits ((Q.board pos d wires bits).result.take j)).length+
        (((Q.tests.result).take k).flatMap checkBits).length≤
      Q.routeRoom wires+Q.tableRoom := by
  have a := (Q.exact_routing_fits_generated_page d wires bits).2.2
  have b := prefix_width (Q.board pos d wires bits).result (fun row=>row.flatMap termBits) j
  have c := prefix_width Q.tests.result checkBits k
  have total := Nat.add_le_add (Nat.add_le_add a b) c
  have e := (Q.exact_affine_and_test_tables_for_this_page pos d wires bits).2.2
  exact total.trans_eq ((Nat.add_assoc _ _ _).trans (congrArg (Q.routeRoom wires+·) e))

theorem true_entry_choice_add_cut
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool)
    (pre post : List (Term Q.S.old ell)) (x : Term Q.S.old ell)
    (tail : List (List (Term Q.S.old ell))) (chosen : List (List Bool))
    (acc : UVBlock Q.S.old ell) (waiting : List (UVBlock Q.S.old ell))
    (cut : ChoiceCut Q.S.pPos Q.codeWidth Q.S.w Q.tests.result (Q.board pos d wires bits).result
      (oneM Q.S.pPos Q.S.degreePos pos).result ((pre++x::post)::tail) chosen acc waiting) :
    let g := choiceOperation Q.S.pPos Q.codeWidth Q.S.w Q.tests.result tail chosen acc
    let done := pre.map (fun t=>(g t).result)
    let suffix := sumUV Q.S.pPos g post
    let next := addM Q.S.pPos (g x) suffix
    (waiting.flatMap leafPayload).length+(chosen.flatten).length+
      (done.flatMap leafPayload).length+(leafPayload acc).length+
      (leafPayload (g x).result).length+(leafPayload suffix.result).length+
      (leafPayload next.result).length≤Q.choiceRoom := by
  have pack := Q.exact_affine_and_test_tables_for_this_page pos d wires bits
  have h := actual_choice_add_cut_uses_bounded_named_registers pre post x pack.2.1 cut
  rw [pack.1] at h
  exact h

theorem true_entry_choice_counter_cut
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool)
    (chosen : List (List Bool)) (acc : UVBlock Q.S.old ell) (waiting : List (UVBlock Q.S.old ell))
    (cut : ChoiceCut Q.S.pPos Q.codeWidth Q.S.w Q.tests.result (Q.board pos d wires bits).result
      (oneM Q.S.pPos Q.S.degreePos pos).result [] chosen acc waiting) :
    let now := evalRows Q.S.pPos Q.codeWidth Q.S.w Q.tests.result [] chosen acc
    now.result=(if (A1R9.checkModes Q.S.w chosen Q.tests.result).result then acc else uvZero Q.S.pPos Q.S.old ell) ∧
    (waiting.flatMap leafPayload).length+(chosen.flatten).length+(leafPayload acc).length+
      (leafPayload now.result).length≤Q.choiceRoom := by
  have pack := Q.exact_affine_and_test_tables_for_this_page pos d wires bits
  have h := actual_choice_test_cut_uses_bounded_named_registers pack.2.1 cut
  rw [pack.1] at h
  exact h

theorem true_entry_canonical_resize_cut {p : ℕ} (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (d : ℕ) (wires : List WireRead) (bits : List Bool) (k : ℕ) :
    (leafPayload (Q.createdValue pos d wires bits).result).length+
       ((leafPayload (Q.delivered hf F pos d wires bits).result).take k).length≤
      Q.W+ell*(F.words.length*p) :=
  packet_word_resize_keeps_a_real_old_operand_and_return (J6R30ProducedGateRegistry.shapeCompatible Q.S hf F.hp F.exactMod)
    (Q.createdValue pos d wires bits).result k


/-- The completed coefficient is needed by the final packet multiply
and is kept while the source-mode product is evaluated. The strict
right fold also keeps actual earlier mode factors, not arbitrary
fills. -/
theorem true_entry_source_mode_cut
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool)
    (prev rest : List (ModeInput Q.S.a Q.S.p Q.S.i Q.S.w))
    (u : ModeInput Q.S.a Q.S.p Q.S.i Q.S.w)
    (order : Q.data.modes=prev++u::rest) :
    let cs := (Q.routed d wires bits).result.2
    let g := sourcePower (q:=Q.S.w) Q.S.pPos Q.S.degreePos pos Q.S.i cs
    let old := prev.map g
    let now := g u
    let tail := sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i cs rest
    Q.moments pos d wires bits=old.foldr (mulM Q.S.pPos) (mulM Q.S.pPos now tail) ∧
    (leafPayload (Q.coefficient pos d wires bits).result).length+
      ((old.map Meter.result).flatMap leafPayload).length+
      (leafPayload now.result).length+(leafPayload tail.result).length+
      (leafPayload (mulM Q.S.pPos now tail).result).length≤(Q.data.modes.length+3)*Q.W := by
  let cs := (Q.routed d wires bits).result.2
  let g := sourcePower (q:=Q.S.w) Q.S.pPos Q.S.degreePos pos Q.S.i cs
  let old := prev.map g
  let now := g u
  let tail := sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i cs rest
  obtain ⟨run,bitsize⟩ :=
    packet_source_product_holds_actual_factors Q.S.pPos Q.S.degreePos pos Q.S.i cs prev rest u
  have len : prev.length+1≤Q.data.modes.length := by
    rw [order,List.length_append,List.length_cons]
    omega
  constructor
  · change sourceProduct Q.S.pPos Q.S.degreePos pos Q.S.i cs Q.data.modes=_
    rw [order]
    exact run
  · change (leafPayload (Q.coefficient pos d wires bits).result).length+
      ((old.map Meter.result).flatMap leafPayload).length+
      (leafPayload now.result).length+(leafPayload tail.result).length+
      (leafPayload (mulM Q.S.pPos now tail).result).length≤_
    have exactSize : ((old.map Meter.result).flatMap leafPayload).length+
      (leafPayload now.result).length+(leafPayload tail.result).length+
      (leafPayload (mulM Q.S.pPos now tail).result).length=(prev.length+3)*Q.W := bitsize
    have w : (leafPayload (Q.coefficient pos d wires bits).result).length=Q.W :=
      leaf_payload_width _
    calc
      _ = (prev.length+4)*Q.W := by
        rw [w]
        have : Q.W+((old.map Meter.result).flatMap leafPayload).length+
          (leafPayload now.result).length+(leafPayload tail.result).length+
          (leafPayload (mulM Q.S.pPos now tail).result).length=
          Q.W+(((old.map Meter.result).flatMap leafPayload).length+
          (leafPayload now.result).length+(leafPayload tail.result).length+
          (leafPayload (mulM Q.S.pPos now tail).result).length) := by ac_rfl
        rw [this,exactSize]
        ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

#print axioms true_entry_source_mode_cut
#print axioms exact_routing_fits_generated_page
#print axioms exact_affine_and_test_tables_for_this_page
#print axioms true_entry_setup_named_payload
#print axioms true_entry_choice_add_cut
#print axioms true_entry_choice_counter_cut
#print axioms true_entry_canonical_resize_cut
end LivePageHit
end J6R68.LeafPeak.Packet


/-! A generated command already in the genuine R66 positive-terminal
read phase. Its row data and its local evaluation are those fetched in
that same live bank. Extend the same outer reserve by the current
packet's named buffers only; the packet result is not charged before
it is made, nor is the command file allocated again. -/
namespace J6R68.LeafPeak.Packet
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R18ChildWrite J6R21Ancestor J6R21Leaf
open J6R22Active J6R24MeteredRecursion J6R33StatefulArithmeticPage J6R48Leaf J6R50Leaf J6R62Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 3500
set_option Elab.async false

variable {f : ℤ[X]} {p ell key prec tw bw page : ℕ}

def pendingLeafWords (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (pre : List (ReadCmd key page))
    (rev : List Bool) (lefts : List (Block F ell)) : ℕ :=
  let bits := (reverseTape rev []).result
  let prior := pre.map (fun u=>(u.read hf F pos B bits).result)
  (lefts.flatMap leafPayload).length+rev.length+bits.length+(prior.flatMap leafPayload).length

theorem pending_before_packet_output (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page) (pre : List (ReadCmd key page))
    (cmd : ReadCmd key page) (rev : List Bool) (lefts : List (Block F ell)) :
    pendingLeafWords hf F pos B pre rev lefts≤liveReadRegisters hf F pos B pre cmd rev lefts := by
  change _≤pendingLeafWords hf F pos B pre rev lefts+_
  exact Nat.le_add_right _ _

/-- Consume the exact current-command equality and formatted-lookup
premise of the frozen R66 leaf. The outside cap can be the previously
verified paused-roster or boot/live reserve for this *same* cut.
The conclusion presents independent setup, current coefficient sum,
and resize cuts, not a double charge for preparing another command. -/
theorem actual_formatted_packet_uses_same_leaf_and_stage_reserve
    (hf : f.Monic) (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (clk : List Unit) (rows pre post : List (ReadCmd key page))
    (id : J6R15ModeCost.Word key) (pg : J6R15ModeCost.Word page) (d : ℕ) (wires : List WireRead)
    (order : rows=pre++(.packet id pg d wires)::post)
    (format : ReadFormat B clk.length (.packet id pg d wires))
    (rev : List Bool) (lefts : List (Block F ell))
    (cut : ClockCut F.hp (actualRowQuery hf F pos B rows) clk [] rev lefts)
    (resident room : ℕ)
    (before : resident+(encodedLeafInputs clk rows+
      liveReadRegisters hf F pos B pre (.packet id pg d wires) rev lefts)≤room) :
    ∃ Q : LivePageHit B id pg,
      let bits := (reverseTape rev []).result
      let fixed := resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)
      let current := (.packet id pg d wires : ReadCmd key page).read hf F pos B bits
      let wf := ell*(F.words.length*p)
      bits.length=clk.length ∧ current.result=(Q.delivered hf F pos d wires bits).result ∧
      actualRowQuery hf F pos B rows bits=
        (pre.map (fun u=>u.read hf F pos B bits)).foldr (mulM F.hp)
          (mulM F.hp current (actualRowQuery hf F pos B post bits)) ∧
      (∀ j k, fixed+(Q.routeBits d wires bits+
        (tableBits ((Q.board pos d wires bits).result.take j)).length+
        ((Q.tests.result.take k).flatMap checkBits).length)≤room+(Q.routeRoom wires+Q.tableRoom)) ∧
      (∀ (rs cs : List (Term Q.S.old ell)) (x : Term Q.S.old ell)
        (tail : List (List (Term Q.S.old ell))) (picked : List (List Bool))
        (prod : UVBlock Q.S.old ell) (waiting : List (UVBlock Q.S.old ell)),
        ChoiceCut Q.S.pPos Q.codeWidth Q.S.w Q.tests.result (Q.board pos d wires bits).result
          (oneM Q.S.pPos Q.S.degreePos pos).result ((rs++x::cs)::tail) picked prod waiting →
        let g := choiceOperation Q.S.pPos Q.codeWidth Q.S.w Q.tests.result tail picked prod
        let earlier := rs.map (fun t=>(g t).result)
        let suffix := sumUV Q.S.pPos g cs
        let next := addM Q.S.pPos (g x) suffix
        let localWork := (waiting.flatMap leafPayload).length+picked.flatten.length+
          (earlier.flatMap leafPayload).length+(leafPayload prod).length+
          (leafPayload (g x).result).length+(leafPayload suffix.result).length+
          (leafPayload next.result).length
        fixed+(Q.routeBits d wires bits+Q.tableSize pos d wires bits+localWork)≤
          room+(Q.routeRoom wires+Q.tableRoom+Q.choiceRoom)) ∧
      (∀ j, fixed+((leafPayload (Q.createdValue pos d wires bits).result).length+
        ((leafPayload (Q.delivered hf F pos d wires bits).result).take j).length)≤room+(Q.W+wf)) := by
  have len := (actual_clock_stop_has_one_forward_tape cut).1
  obtain ⟨Q⟩ := exists_live_page_for_actual_command B clk.length id pg d wires format
  let bits := (reverseTape rev []).result
  have waiting := pending_before_packet_output hf F pos B pre (.packet id pg d wires) rev lefts
  have fixed : resident+(encodedLeafInputs clk rows+pendingLeafWords hf F pos B pre rev lefts)≤room :=
    (Nat.add_le_add_left (Nat.add_le_add_left waiting _) _).trans before
  have same := congrArg Meter.result (Q.actual_read_returns_this_creation_value_and_charges_it_once hf F pos d wires bits).1
  refine ⟨Q,len,same,?_,?_,?_,?_⟩
  · change actualRowQuery hf F pos B rows bits=_
    rw [order]
    exact read_product_has_that_exact_pending_context hf F pos B pre post (.packet id pg d wires) bits
  · intro j k
    exact Nat.add_le_add fixed (Q.true_entry_setup_named_payload pos d wires bits j k)
  · intro rs cs x tail picked prod older h
    have stage := Q.true_entry_choice_add_cut pos d wires bits rs cs x tail picked prod older h
    exact Nat.add_le_add fixed
      (Nat.add_le_add (Nat.add_le_add (Q.exact_routing_fits_generated_page d wires bits).2.2
        (Q.exact_affine_and_test_tables_for_this_page pos d wires bits).2.2.le) stage)
  · intro j
    exact Nat.add_le_add fixed (Q.true_entry_canonical_resize_cut hf F pos d wires bits j)

#print axioms pending_before_packet_output
#print axioms actual_formatted_packet_uses_same_leaf_and_stage_reserve
end J6R68.LeafPeak.Packet
