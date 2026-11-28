import J6R17ModeTapeLayout
import J6R14LayoutCostPoly
import V8NativeMessageN2DLabelsSelector

/-! At a fixed full-64 source selection, the actual paid label incidences
can be fed straight to the original fixed exporter. Their rounded copy
word is that of the same selector. This does not identify the two choices
of within-cell seat order. -/
namespace J6R68ActiveInputs
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R10Repack P11FullPacking
open J6R12CollisionEdges J6R12CollisionMenu J6R12CollisionSource J6R12CollisionGreedyStep
open J6R11CollisionReindex J6R14LayoutCost J6R17ModeTape
open J6ActiveRun J6R9Recursive J6R11Blueprint J6R12Blueprint
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 3200
set_option Elab.async false

section Source
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable {N : Network E R C} (I : Full64Input N a) (P : PhysicalPacking N a (Fin 64))

def paidFixedOutput (q : ℕ) : Meter PackedTape :=
  let input := I.run
  let F := I.format
  let x := packFixed F.kR F.kC F.b q a input.result.1
  ⟨x.result,input.steps+x.steps+6⟩

theorem source_pages_of_same_selected_labels (q : ℕ) (rounded : RoundsExactly P) :
    sourcePages I.format (wordsOf P) q=P.copies := by
  let z := wordsOf P
  have hF : Fintype.card (Fin a→Fin 64)=2^I.format.b := by
    rw [I.labelWidth,source_alphabet (G:=Fin 64) (by simp) a]
  have cells : (fun e=>pairedWords a (Fin 64) (sourceCell I.format z e))=
    declaredCell N P.rowLabel P.colLabel := by
    funext e
    simp only [sourceCell,I.rowExact,I.colExact]
    rfl
  change P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) at rounded
  rw [sourcePages,peakSource_exact I.format hF z q,rounded,←cells,maxFiber_transport]

theorem fixed_export_of_same_paid_labels (q : ℕ) (hq : 0<q) (ha : a≤q)
    (fit : Fintype.card E<2^q) (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) :
    let F := I.format
    let raw := paidFixedOutput I q
    raw.result.copies.length=q+1 ∧ bitsValue raw.result.copies=P.copies ∧
      (∃ cs : List (P11FullPacking.Cell (Fin a) (Fin 64)),
        raw.result.boxes.map headerOf=cs.map encodeHeader ∧ cs.Nodup ∧ ∀ c,c∈cs) ∧
      raw.result.boxes.length=2^(6*a)*2^(6*a) ∧ exportRows raw.result.boxes=Fintype.card E ∧
      raw.steps≤I.run.steps+packFixedCap F.kR F.kC F.b q a (Fintype.card E)+6 := by
  obtain ⟨width,cp,box,_,fee⟩ :=
    packFixed_exact I.format I.labelWidth coord (wordsOf P) q hq ha fit
  obtain ⟨cs,header,nd,all,nbox,_,rows⟩ :=
    packed_header_lift I.format I.labelWidth (wordsOf P) box
  dsimp only [paidFixedOutput]
  rw [caught]
  exact ⟨width,cp.trans (source_pages_of_same_selected_labels I P q rounded),
    ⟨cs,header,nd,all⟩,nbox,rows,Nat.add_le_add_right (Nat.add_le_add_left fee _) _⟩

def activeLayoutFromPaidLabels (q : ℕ) (hq : 0<q) (ha : a≤q)
    (fit : Fintype.card E<2^q) (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) : Meter (LayoutReceipt a P.copies (q+1) (Fintype.card E)) :=
  let raw := paidFixedOutput I q
  let h := fixed_export_of_same_paid_labels I P q hq ha fit coord caught rounded
  ⟨⟨raw.result.boxes,⟨raw.result.copies,h.1⟩,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩,raw.steps⟩

theorem active_layout_reuses_the_exact_payload (q : ℕ) (hq : 0<q) (ha : a≤q)
    (fit : Fintype.card E<2^q) (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) :
    let A := activeLayoutFromPaidLabels I P q hq ha fit coord caught rounded
    let W := paidFixedOutput I q
    A.result.boxes=W.result.boxes ∧ A.result.copies.bits=W.result.copies ∧ A.steps=W.steps :=
  ⟨rfl,rfl,rfl⟩
end Source

#print axioms source_pages_of_same_selected_labels
#print axioms fixed_export_of_same_paid_labels
#print axioms active_layout_reuses_the_exact_payload
end J6R68ActiveInputs
