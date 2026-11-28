import J6R94HeldOwnerProviderHeaderWriter
import J6R51OnlineCore
import J6R49SourceLayoutOwners

/-! Standalone actual grouped-header producer for the physical chart
used by a ticket. Isolated owners enter through the full emitted
label field, and never through an edge-only inference. -/
namespace J6R94HeldOwnerProvider
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply J6R26DescriptorTree
open J6R49SourceLayout J6R54ExteriorOwner J6R14LayoutCost J6R68ActiveInputs
open J6R24MeteredRecursion J6R52CacheSource J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R50SourceProducer
open J6R34ChildPath J6R34RootAtlas J6R32StatefulArithmetic J6R10Reachable
open V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 5200
set_option maxHeartbeats 32000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

local instance graphFinite : Fintype v.parent.host.Edge := v.parent.host.finiteEdge

section Emit
structure SameRawGroupChart
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape)
    (axisBits : List Bool) (names : List (Word Y.site.ownerWidth)) : Prop where
  cachedLabels : raw.vertexLabels=(runWithIngress I q W).result.vertexLabels
  selectedLabels : I.run.result.2=I.order.map (fun x=>I.format.label (wordsOf (layout T v) x))
  serialized : ∀ u : Fin ((SP).levelBits v.parent.depth)→Fin 64,I.format.label u=coordinateLabel u
  actualAxis : axisBits=Y.input.words.result.axis
  declaredNames : names=I.order.map Y.site.oldKey

theorem literal_greedy_headers_charge_only_emitted_owner_words
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape)
    (axisBits : List Bool) (names : List (Word Y.site.ownerWidth))
    (h : SameRawGroupChart Y I W q raw axisBits names) :
    let read := writeCurrentGroupHeaders axisBits names raw.vertexLabels
    read.result=some (I.order.map (ownerGroupRow Y.site)) ∧
      read.steps≤3+I.order.length*groupHeaderUnit Y.site.ownerWidth (axis T v).val := by
  let a := axis T v
  have fit : axisBits.length=a.val := (congrArg List.length h.actualAxis).trans Y.input.clock
  have rawSame : raw.vertexLabels=I.order.map (fun x=>coordinateLabel (wordsOf (layout T v) x)) := by
    rw [h.cachedLabels,chosen_greedy_output_preserves_complete_vertex_words,h.selectedLabels]
    simp only [h.serialized]
  have chart : (I.order.map (fun x=>⟨Y.site.oldKey x,word (q:=6) ((wordsOf (layout T v) x) a).val⟩))=
      I.order.map (ownerGroupRow Y.site) := by
    apply List.map_congr_left
    intro vtx _
    cases vtx <;> rfl
  have paid := complete_group_headers_from_exact_words a axisBits fit I.order Y.site.oldKey (wordsOf (layout T v))
  dsimp only at paid ⊢
  rw [h.declaredNames,rawSame,←chart,←fit]
  exact paid

/-- This local producer consumes an already computed, actually carried
    layout result. It does not call the layout solver again. -/
def headersFromLiveGreedy
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape)
    (axisBits : List Bool) (names : List (Word Y.site.ownerWidth))
    (h : SameRawGroupChart Y I W q raw axisBits names) :
    Meter (ParentOwnerHeaders Y.site) :=
  let op := writeCurrentGroupHeaders axisBits names raw.vertexLabels
  let checked := (literal_greedy_headers_charge_only_emitted_owner_words Y I W q raw axisBits names h).1
  let ok := unwrapSuccess op (by rw [checked]; rfl)
  ⟨⟨I.order,I.distinct,I.complete,ok.result,
    congrArg Meter.result (unwrap_success_exact op _ _ checked)⟩,ok.steps⟩

theorem genuine_carried_labels_produce_all_grouped_headers
    (I : CallFormat (printedParams (f:=f) (ell:=ell) s) v.parent)
    (W : Ingress I) (q : ℕ) (raw : GreedyPackedTape)
    (axisBits : List Bool) (names : List (Word Y.site.ownerWidth))
    (h : SameRawGroupChart Y I W q raw axisBits names) :
    let H := headersFromLiveGreedy Y I W q raw axisBits names h
    H.result.raw=I.order.map (ownerGroupRow Y.site) ∧
      H.steps≤3+I.order.length*groupHeaderUnit Y.site.ownerWidth (axis T v).val := by
  let op := headersFromLiveGreedy Y I W q raw axisBits names h
  exact ⟨op.result.same,(literal_greedy_headers_charge_only_emitted_owner_words Y I W q raw axisBits names h).2⟩
end Emit

/-- No equivalence of arbitrary old layouts is asserted: the same
    full-64 selected packing gives the complete label receipt directly. -/
theorem original_full64_selector_supplies_complete_owner_labels
    (inputs : Full64PlanInputs SP (sourceDelta s))
    (same : packing (forget (full64Selector inputs)) (ticketReady T v)=layout T v) :
    let I := inputs v.parent (ticketReady T v)
    I.run.result.2=I.order.map (fun x=>I.format.label (wordsOf (layout T v) x)) := by
  have full := (full64_selected_receipt inputs (ticketReady T v)).2.2.1
  rw [same] at full
  exact full

#print axioms literal_greedy_headers_charge_only_emitted_owner_words
#print axioms genuine_carried_labels_produce_all_grouped_headers
#print axioms original_full64_selector_supplies_complete_owner_labels
end
end J6R94HeldOwnerProvider