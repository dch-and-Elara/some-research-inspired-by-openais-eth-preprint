import J6R75RawPeakLayoutWords

/-! The ordered lookup buckets in the actual fixed export: retain
the original key and tag inputs, actual completed earlier group
results, and current/suffix/assembled records with their true widths.
This is not transfer from a byte-wise different packet ordering. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R14LayoutCost J6R12CollisionMenu P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10800000
set_option maxRecDepth 3950
set_option Elab.async false

def literalGroupReturn {A : Type*} (b q : ℕ)
    (key : CellWord) (one : Meter (List A×List Bool))
    (later : Meter (List (Box A)×List Bool)) :
    Meter (List (Box A)×List Bool) :=
  let mx := maxWord q one.result.2 later.result.2
  ⟨(⟨key,one.result.1,one.result.2⟩::later.result.1,mx.result),
    one.steps+later.steps+mx.steps+4*b+2*q+8⟩

def actualGroupFrame {A : Type*} (view : A→EdgeTape) (kR kC b q : ℕ)
    (es : List A) (k : CellWord) : Box A :=
  let run := groupOne view kR kC b q k es
  ⟨k,run.result.1,run.result.2⟩

theorem actual_layout_group_cut_has_its_original_pending_boxes
    {A : Type*} (view : A→EdgeTape) (kR kC b q : ℕ) (es : List A)
    (pre : List CellWord) (key : CellWord) (post : List CellWord) :
    let group := groupAll view kR kC b q es
    let one := fun k=>groupOne view kR kC b q k es
    let frame := actualGroupFrame view kR kC b q es
    let current := literalGroupReturn b q key (one key) (group post)
    group (pre++key::post)=(pre.map (fun k=> (k,one k))).foldr
      (fun k r=>literalGroupReturn b q k.1 k.2 r) current ∧
    (group (pre++key::post)).result.1=pre.map frame++frame key::(group post).result.1 := by
  induction pre with
  | nil=>exact ⟨rfl,rfl⟩
  | cons k ks ih=>
    let group := groupAll view kR kC b q es
    let one := fun k=>groupOne view kR kC b q k es
    constructor
    · change literalGroupReturn b q k (one k) (group (ks++key::post))=
        literalGroupReturn b q k (one k) _
      exact congrArg (literalGroupReturn b q k (one k)) ih.1
    · exact congrArg (actualGroupFrame view kR kC b q es k::·) ih.2

section Scope
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)

theorem actual_fixed_layout_grouping_retains_one_budget_of_named_words
    (q : ℕ) (hq : 0<q) (fits : Fintype.card E<2^q)
    (pre : List CellWord) (key : CellWord) (post : List CellWord)
    (split : (allPairsMachine F.b).result=pre++key::post)
    (resident roof : ℕ) (live : resident≤roof) :
    let es := F.graph (fun v=>some (z v))
    let tags := tagAll F.kR F.kC F.b q es
    let keys := allPairsMachine F.b
    let plan := groupAll Tagged.edge F.kR F.kC F.b q tags.result
    let frame := actualGroupFrame Tagged.edge F.kR F.kC F.b q tags.result
    let past := pre.map frame
    let later := plan post
    let present := frame key
    let whole := plan keys.result
    let full := orderedTape F.kR F.kC F.b q es
    let b := F.b
    let M := Fintype.card E
    let N := 2^b*2^b
    let w := q+fullEdgeLayoutWidth F.kR F.kC b
    full.result=whole.result ∧
    whole.result.1=past++present::later.result.1 ∧
    whole.result.1=sourceBoxes F z q ∧
    resident+(rawLayoutBits rawEdgeLayoutBits es+
      rawLayoutBits rawTaggedLayoutBits tags.result+rawLayoutBits rawCellLayoutBits keys.result+
      (rawLayoutBits rawBoxLayoutBits past+rawBoxLayoutBits present+rawLayoutBits rawBoxLayoutBits later.result.1)+
      rawLayoutBits rawBoxLayoutBits whole.result.1+3*q)≤
      roof+(fullEdgeLayoutWidth F.kR F.kC b*M+w*M+(2*b)*N+
        2*((2*b+q)*N+w*M)+3*q) := by
  let es := F.graph (fun v=>some (z v))
  let tags := tagAll F.kR F.kC F.b q es
  let keys := allPairsMachine F.b
  let plan := groupAll Tagged.edge F.kR F.kC F.b q tags.result
  let frame := actualGroupFrame Tagged.edge F.kR F.kC F.b q tags.result
  let past := pre.map frame
  let present := frame key
  let later := plan post
  let whole := plan keys.result
  have edgeCount : es.length<2^q := by rwa [sourceGraph_len F z]
  have tagEq : tags.result=tagSpec q 0 es := (tagAll_exact F.kR F.kC F.b q hq es edgeCount).1
  have groupEq : whole.result.1=sourceBoxes F z q :=
    (orderedTape_exact F.kR F.kC F.b q hq es edgeCount (graphWord_widths F z)).1
  have cut : whole.result.1=past++present::later.result.1 := by
    change (plan keys.result).result.1=_
    rw [split]
    exact (actual_layout_group_cut_has_its_original_pending_boxes Tagged.edge F.kR F.kC F.b q
      tags.result pre key post).2
  have selected : rawLayoutBits rawBoxLayoutBits past+rawBoxLayoutBits present+
      rawLayoutBits rawBoxLayoutBits later.result.1=rawLayoutBits rawBoxLayoutBits whole.result.1 := by
    rw [cut,raw_layout_bits_append]
    change rawLayoutBits rawBoxLayoutBits past+rawBoxLayoutBits present+
        rawLayoutBits rawBoxLayoutBits later.result.1=
      rawLayoutBits rawBoxLayoutBits past+(rawBoxLayoutBits present+rawLayoutBits rawBoxLayoutBits later.result.1)
    exact Nat.add_assoc _ _ _
  have d := source_graph_layout_bytes_are_exact F z
  have t : rawLayoutBits rawTaggedLayoutBits tags.result=
      (q+fullEdgeLayoutWidth F.kR F.kC F.b)*Fintype.card E := by
    rw [tagEq]
    exact entire_source_tag_tape_has_actual_bit_width F z q
  have k := actual_pair_key_table_bits F.b
  have all : rawLayoutBits rawBoxLayoutBits whole.result.1=
      (2*F.b+q)*(2^F.b*2^F.b)+(q+fullEdgeLayoutWidth F.kR F.kC F.b)*Fintype.card E := by
    rw [groupEq]
    exact actual_source_boxes_have_their_grouped_word_width F z q
  refine ⟨rfl,cut,groupEq,Nat.add_le_add live ?_⟩
  change rawLayoutBits rawEdgeLayoutBits es+rawLayoutBits rawTaggedLayoutBits tags.result+
    rawLayoutBits rawCellLayoutBits keys.result+
    (rawLayoutBits rawBoxLayoutBits past+rawBoxLayoutBits present+rawLayoutBits rawBoxLayoutBits later.result.1)+
    rawLayoutBits rawBoxLayoutBits whole.result.1+3*q≤_
  rw [d,t,k,selected,all]
  omega
end Scope

#print axioms actual_layout_group_cut_has_its_original_pending_boxes
#print axioms actual_fixed_layout_grouping_retains_one_budget_of_named_words
end J6R75RawPeak
