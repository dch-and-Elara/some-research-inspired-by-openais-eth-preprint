import J6R75RawPeakLayoutReturn
import J6R75RawPeakLayoutIngress

/-! Real greedy handoff to the fixed ordered-cell exporter. Its
actual labeled intermediate, not a separately equal final layout,
selects every subsequent bucket and packet-writing phase. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionPacking
open J6R12CollisionSource J6R12CollisionMenu J6R14LayoutCost J6R68ActiveInputs
open J6R10Repack J6R11CollisionReindex J6R17ModeTape P11FullPacking
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16500000
set_option maxRecDepth 4550
set_option Elab.async false

def ingressRetainRoof (kR kC b vertices edges : ℕ) : ℕ :=
  (1+max kR kC)*vertices+(kR+kC)*edges+(kR+kC+2)*edges+b*vertices

def rawGroupingWorkRoof (kR kC b q M : ℕ) : ℕ :=
  fullEdgeLayoutWidth kR kC b*M+(q+fullEdgeLayoutWidth kR kC b)*M+
    (2*b)*(2^b*2^b)+2*fixedLayoutGroupBits kR kC b q M+3*q

def rawExportWorkRoof (a kR kC b q M : ℕ) : ℕ :=
  fullEdgeLayoutWidth kR kC b*M+fixedLayoutGroupBits kR kC b q M+
    (q+1)+2*fixedLayoutExportBits a kR kC b q M

section Native
variable {E R C : Type*} [Fintype E] [Fintype R] [Fintype C] {a : ℕ}
variable {N : Network E R C} (I : Full64Input N a) (W : Ingress I)

def rawIngressRetainedBits : ℕ :=
  let F := I.format
  let inlet := initGraph F.kR F.kC W.paid.result.2
  let marked := drive F.e F.kR F.kC F.b W.paid.result.1 inlet.result
  rawLayoutBits rawLayoutTargetBits W.paid.result.1+
    rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+
    rawLayoutBits rawEdgeLayoutBits inlet.result+
    gridMemoryBits marked.result.2

def LiteralRawLayoutPhases (rank : ℕ) (z : R⊕C→Fin a→Fin 64)
    (resident roof : ℕ) : Prop :=
  let F := I.format
  let es := F.graph (fun x=>some (z x))
  let inlet := initGraph F.kR F.kC W.paid.result.2
  let marked := drive F.e F.kR F.kC F.b W.paid.result.1 inlet.result
  let actual := runWithIngress I rank W
  let packed := packFixed F.kR F.kC F.b rank a es
  let tags := tagAll F.kR F.kC F.b rank es
  let keys := allPairsMachine F.b
  let group := groupAll Tagged.edge F.kR F.kC F.b rank tags.result
  let frame := actualGroupFrame Tagged.edge F.kR F.kC F.b rank tags.result
  let stock := groupedCopies a F.kR F.kC F.b rank es
  let exportBoxAt := exportBox F.kR F.kC F.b rank a
  let exportTail := exportTape F.kR F.kC F.b rank a
  let held := resident+rawIngressRetainedBits I W
  let H := ingressRetainRoof F.kR F.kC F.b I.order.length (Fintype.card E)
  let J := rawGroupingWorkRoof F.kR F.kC F.b rank (Fintype.card E)
  let K := rawExportWorkRoof a F.kR F.kC F.b rank (Fintype.card E)
  let room := (roof+H)+max J K
  marked.result.1=es ∧
  actual.result.boxes=packed.result.boxes ∧ actual.result.copies=packed.result.copies ∧
  actual.result.vertexLabels=marked.result.2 ∧
  held≤roof+H ∧
  (∀ pre key post,keys.result=pre++key::post →
    (group keys.result).result.1=(pre.map frame)++frame key::(group post).result.1 ∧
    held+(rawLayoutBits rawEdgeLayoutBits es+rawLayoutBits rawTaggedLayoutBits tags.result+
      rawLayoutBits rawCellLayoutBits keys.result+
      (rawLayoutBits rawBoxLayoutBits (pre.map frame)+rawBoxLayoutBits (frame key)+
        rawLayoutBits rawBoxLayoutBits (group post).result.1)+
      rawLayoutBits rawBoxLayoutBits (group keys.result).result.1+3*rank)≤room) ∧
  (∀ pre one post,stock.result.1=pre++one::post →
    actual.result.boxes=(pre.map (fun x=>(exportBoxAt x).result))++
      (exportBoxAt one).result::(exportTail post).result ∧
    held+(rawLayoutBits rawEdgeLayoutBits es+rawLayoutBits rawBoxLayoutBits stock.result.1+
      actual.result.copies.length+
      (rawLayoutBits rawExportLayoutBits (pre.map (fun x=>(exportBoxAt x).result))+
        rawExportLayoutBits (exportBoxAt one).result+rawLayoutBits rawExportLayoutBits (exportTail post).result)+
      rawLayoutBits rawExportLayoutBits actual.result.boxes)≤room)

theorem true_greedy_layout_groups_and_exports_with_its_named_ingress_live
    (rank : ℕ) (hq : 0<rank) (dim : a≤rank) (legal : Fintype.card E<2^rank)
    (coord : ∀ v,I.format.label v=coordinateLabel v)
    (z : R⊕C→Fin a→Fin 64) (caught : I.run.result.1=I.format.graph (fun x=>some (z x)))
    (resident roof : ℕ) (base : resident≤roof) :
    LiteralRawLayoutPhases I W rank z resident roof := by
  let F := I.format
  let es := F.graph (fun x=>some (z x))
  let inlet := initGraph F.kR F.kC W.paid.result.2
  let marked := drive F.e F.kR F.kC F.b W.paid.result.1 inlet.result
  let actual := runWithIngress I rank W
  let packed := packFixed F.kR F.kC F.b rank a es
  let held := resident+rawIngressRetainedBits I W
  let H := ingressRetainRoof F.kR F.kC F.b I.order.length (Fintype.card E)
  let J := rawGroupingWorkRoof F.kR F.kC F.b rank (Fintype.card E)
  let K := rawExportWorkRoof a F.kR F.kC F.b rank (Fintype.card E)
  obtain ⟨cmd,wire,start⟩ := actual_ingress_commands_and_wire_bytes_have_their_source_capacity I W
  obtain ⟨reuses,allLabels,allBoxes,allCopies,labelsSize⟩ :=
    actual_ingress_greedy_keeps_the_complete_original_label_file I W rank
  have same : marked.result.1=es := (congrArg Prod.fst reuses).trans caught
  have boxes : actual.result.boxes=packed.result.boxes := by
    rw [show actual.result.boxes=(packFixed F.kR F.kC F.b rank a marked.result.1).result.boxes from allBoxes,same]
  have copies : actual.result.copies=packed.result.copies := by
    rw [show actual.result.copies=(packFixed F.kR F.kC F.b rank a marked.result.1).result.copies from allCopies,same]
  have inCap : rawIngressRetainedBits I W≤H := by
    unfold rawIngressRetainedBits H ingressRetainRoof
    dsimp only
    rw [wire,start,labelsSize]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right cmd _) _) _
  have room : held≤roof+H := Nat.add_le_add base inCap
  refine ⟨same,boxes,copies,allLabels,room,?_,?_⟩
  · intro pre key post hit
    obtain ⟨_,result,_,fits⟩ :=
      actual_fixed_layout_grouping_retains_one_budget_of_named_words F z rank hq legal pre key post
        hit held (roof+H) room
    exact ⟨result,fits.trans (Nat.add_le_add_left (Nat.le_max_left J K) _)⟩
  · intro pre one post hit
    obtain ⟨boxed,_,order,fits⟩ :=
      same_fixed_export_has_original_groups_and_named_export_workspace F z I.labelWidth coord rank hq dim legal
        pre one post hit held (roof+H) room
    refine ⟨boxes.trans (boxed.trans order),?_⟩
    rw [boxes,copies]
    exact fits.trans (Nat.add_le_add_left (Nat.le_max_right J K) _)
end Native

#print axioms true_greedy_layout_groups_and_exports_with_its_named_ingress_live
end J6R75RawPeak
