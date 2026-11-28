import J6R75RawPeakLayoutExport
import J6R75RawPeakLayoutGroup

/-! The actual R14 serialized export recursion, with all past boxes
in original order, and the selected co-live grouped and returned
tapes of the true packFixed, not the result of calling a new pack. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R14LayoutCost J6R12CollisionMenu
open J6R17ModeTape P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4250
set_option Elab.async false

def literalLayoutExportReturn (x : Meter ExportBox) (old : Meter (List ExportBox)) :
    Meter (List ExportBox) := ⟨x.result::old.result,x.steps+old.steps+6⟩

theorem actual_layout_export_cut_retains_real_returned_boxes
    (kR kC b q a : ℕ) (pre : List (Box Tagged)) (one : Box Tagged) (post : List (Box Tagged)) :
    let single := exportBox kR kC b q a
    let emitBoxes := exportTape kR kC b q a
    emitBoxes (pre++one::post)=(pre.map single).foldr literalLayoutExportReturn
      (literalLayoutExportReturn (single one) (emitBoxes post)) ∧
    (emitBoxes (pre++one::post)).result=(pre.map (fun x=>(single x).result))++
      (single one).result::(emitBoxes post).result := by
  induction pre with
  | nil=>exact ⟨rfl,rfl⟩
  | cons x xs ih=>
    let single := exportBox kR kC b q a
    let out := exportTape kR kC b q a
    constructor
    · exact congrArg (literalLayoutExportReturn (single x)) ih.1
    · exact congrArg ((single x).result::·) ih.2

def fixedLayoutExportBits (a kR kC b q M : ℕ) : ℕ :=
  (2*b+16*a)*(2^b*2^b)+((q+fullEdgeLayoutWidth kR kC b)+(a+q))*M

def fixedLayoutGroupBits (kR kC b q M : ℕ) : ℕ :=
  (2*b+q)*(2^b*2^b)+(q+fullEdgeLayoutWidth kR kC b)*M

section Source
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)

theorem same_fixed_export_has_original_groups_and_named_export_workspace
    (alphabet : F.b=6*a) (labels : ∀ v,F.label v=coordinateLabel v)
    (q : ℕ) (hq : 0<q) (low : a≤q) (fits : Fintype.card E<2^q)
    (pre : List (Box Tagged)) (one : Box Tagged) (post : List (Box Tagged))
    (split : (groupedCopies a F.kR F.kC F.b q (F.graph (fun x=>some (z x)))).result.1=pre++one::post)
    (resident roof : ℕ) (live : resident≤roof) :
    let g := F.graph (fun x=>some (z x))
    let groups := groupedCopies a F.kR F.kC F.b q g
    let all := packFixed F.kR F.kC F.b q a g
    let w := exportTape F.kR F.kC F.b q a groups.result.1
    let E₁ := exportBox F.kR F.kC F.b q a
    let earlier := pre.map (fun x=>(E₁ x).result)
    let here := (E₁ one).result
    let later := (exportTape F.kR F.kC F.b q a post).result
    let M := Fintype.card E
    all.result.boxes=w.result ∧ all.result.copies=groups.result.2 ∧
    w.result=earlier++here::later ∧
    resident+(rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawBoxLayoutBits groups.result.1+
      all.result.copies.length+(rawLayoutBits rawExportLayoutBits earlier+
        rawExportLayoutBits here+rawLayoutBits rawExportLayoutBits later)+
        rawLayoutBits rawExportLayoutBits all.result.boxes)≤
      roof+(fullEdgeLayoutWidth F.kR F.kC F.b*M+fixedLayoutGroupBits F.kR F.kC F.b q M+
        (q+1)+2*fixedLayoutExportBits a F.kR F.kC F.b q M) := by
  let g := F.graph (fun x=>some (z x))
  let groups := groupedCopies a F.kR F.kC F.b q g
  let all := packFixed F.kR F.kC F.b q a g
  let w := exportTape F.kR F.kC F.b q a groups.result.1
  let E₁ := exportBox F.kR F.kC F.b q a
  let earlier := pre.map (fun x=>(E₁ x).result)
  let here := (E₁ one).result
  let later := (exportTape F.kR F.kC F.b q a post).result
  have exactGroup : groups.result.1=sourceBoxes F z q :=
    (groupedCopies_exact a F.kR F.kC F.b q hq g
      (by rwa [sourceGraph_len F z]) (graphWord_widths F z)).1
  have gwidth :
    rawLayoutBits rawBoxLayoutBits groups.result.1=fixedLayoutGroupBits F.kR F.kC F.b q (Fintype.card E) := by
    rw [exactGroup]
    exact actual_source_boxes_have_their_grouped_word_width F z q
  obtain ⟨actualOut,copy⟩ :=
    actual_fixed_export_writes_exactly_the_source_payload F z alphabet labels q hq low fits
  have wcut : w.result=earlier++here::later := by
    unfold w
    rw [show groups.result.1=pre++one::post from split]
    exact (actual_layout_export_cut_retains_real_returned_boxes F.kR F.kC F.b q a pre one post).2
  have output : all.result.boxes=w.result := rfl
  have joined : rawLayoutBits rawExportLayoutBits earlier+rawExportLayoutBits here+
      rawLayoutBits rawExportLayoutBits later=rawLayoutBits rawExportLayoutBits all.result.boxes := by
    rw [output,wcut,raw_layout_bits_append]
    change rawLayoutBits rawExportLayoutBits earlier+rawExportLayoutBits here+
        rawLayoutBits rawExportLayoutBits later=
       rawLayoutBits rawExportLayoutBits earlier+(rawExportLayoutBits here+rawLayoutBits rawExportLayoutBits later)
    exact Nat.add_assoc _ _ _
  refine ⟨output,rfl,wcut,Nat.add_le_add live ?_⟩
  change rawLayoutBits rawEdgeLayoutBits g+rawLayoutBits rawBoxLayoutBits groups.result.1+
    all.result.copies.length+(rawLayoutBits rawExportLayoutBits earlier+
      rawExportLayoutBits here+rawLayoutBits rawExportLayoutBits later)+
      rawLayoutBits rawExportLayoutBits all.result.boxes≤_
  rw [source_graph_layout_bytes_are_exact F z,gwidth,show all.result.copies.length=q+1 from copy,joined]
  have outBits : rawLayoutBits rawExportLayoutBits all.result.boxes=
    fixedLayoutExportBits a F.kR F.kC F.b q (Fintype.card E) := actualOut
  rw [outBits]
  omega
end Source

#print axioms actual_layout_export_cut_retains_real_returned_boxes
#print axioms same_fixed_export_has_original_groups_and_named_export_workspace
end J6R75RawPeak
