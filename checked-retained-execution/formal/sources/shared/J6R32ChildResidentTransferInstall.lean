import J6R32ChildResidentTransferIdentity

/-! A paid full seat table aligned to every real edge of the actual
greedy chart. The new chart's embedding is the stable address from the
exporter itself, then the proven nonzero legal page convention. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open P11FullPacking J6R14LayoutCost J6R24LegalLayout J6R27OriginalGate J6R15ModeCost
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource J6R11CollisionReindex
open J6R9PacketScopes J6R10Repack J6R17ModeTape J6R20Ancestor
set_option maxHeartbeats 18500000
set_option maxRecDepth 2400

def seatOutput {a w : ℕ} (axis : List Bool) (p : SeatedItem) :
    SeatField a (w+13*a) := (writeMaskedSeat a w axis (itemAnchor p)).result

def writeSeatedBoxes (a w : ℕ) (axis : List Bool) :
    List ExportBox→Meter (List (SeatField a (w+13*a)))
  | []=>⟨[],0⟩
  | x::xs=>
    let L := mapMeter (fun y=>writeMaskedSeat a w axis (itemAnchor (x,y))) x.rows
    let R := writeSeatedBoxes a w axis xs
    ⟨L.result ++ R.result,L.steps+R.steps+(maskedSeatFee a w+6)*x.rows.length+5⟩

theorem write_seated_boxes_exact (a w : ℕ) (axis : List Bool) (boxes : List ExportBox)
    (h : ∀ p∈seatedItems boxes,(writeMaskedSeat a w axis (itemAnchor p)).steps≤maskedSeatFee a w) :
    let W := writeSeatedBoxes a w axis boxes
    W.result=(seatedItems boxes).map (seatOutput (a:=a) (w:=w) axis) ∧
      W.steps≤(2*maskedSeatFee a w+12)*exportRows boxes+5*boxes.length := by
  induction boxes with
  | nil => simp [writeSeatedBoxes,seatedItems,exportRows]
  | cons x xs ih =>
    have hx (y : Seated) (mem : y∈x.rows) : (x,y)∈seatedItems (x::xs) :=
      List.mem_flatMap.mpr ⟨x,List.mem_cons_self,List.mem_map.mpr ⟨y,mem,rfl⟩⟩
    have tl (p : SeatedItem) (mem : p∈seatedItems xs) : p∈seatedItems (x::xs) := by
      unfold seatedItems
      rw [List.flatMap_cons,List.mem_append]
      exact Or.inr mem
    obtain ⟨rv,rc⟩ := ih (fun p hp=>h p (tl p hp))
    obtain ⟨lv,lc⟩ := mapMeter_exact (fun y=>writeMaskedSeat a w axis (itemAnchor (x,y)))
      (fun y=>seatOutput (a:=a) (w:=w) axis (x,y)) (maskedSeatFee a w) x.rows
      (fun y hy=>⟨rfl,h (x,y) (hx y hy)⟩)
    constructor
    · simp only [writeSeatedBoxes,lv,rv,seatedItems,List.flatMap_cons,List.map_append,List.map_map]
      rfl
    · dsimp only [writeSeatedBoxes]
      rw [show exportRows (x::xs)=x.rows.length+exportRows xs by simp [exportRows],List.length_cons]
      nlinarith only [lc,rc]

section Exact
variable {E R C : Type} [Fintype E] {a q : ℕ} {N : Network E R C}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)
variable (P : PhysicalPacking N a (Fin 64))
variable (hrow : F.row=N.row) (hcol : F.col=N.col)
variable (hb : F.b=6*a) (hf : ∀ x,F.label x=coordinateLabel x)
variable (labels : ∀ v,Sum.elim P.rowLabel P.colLabel v=z v)
variable (ha : a≤q) (fit : Fintype.card E<2^q)
variable {xs : List ExportBox}
variable (rel : List.Forall₂ (boxFaithful a P.copies q) (sourceBoxes F z q) xs)
variable (perm : (xs.flatMap (fun x=>x.rows.map Seated.tag)).Perm
  (tagSpec q 0 (F.graph (fun v=>some (z v)))))

noncomputable def packedRowOrigin (x : Observed xs) :
    SeatedOrigin a P.copies q (sourceBoxes F z q) x.val :=
  Classical.choice (seated_item_origin rel
    (fun B h=>by obtain ⟨_,_,e,_,_⟩ := sourceBoxes_valid F hb hf z q fit B h; exact e) x.val x.property)

include perm in
theorem stable_row_address_inj :
    Function.Injective (fun x : Observed xs=>
      stableItem ha (packedRowOrigin F z P hb hf fit rel x)) := by
  intro x y h
  have hTag := same_stable_seat_same_tag F z q ha
    (packedRowOrigin F z P hb hf fit rel x) (packedRowOrigin F z P hb hf fit rel y) h
  have tx := item_ordinal_exact F z q perm x
  have ty := item_ordinal_exact F z q perm y
  exact (item_ordinals_bijective F z q fit perm).1
      (ordinal_tag_injective F z q fit (tx.symm.trans (hTag.trans ty)))

include hrow hcol labels in
theorem stable_row_ordered_cell (x : Observed xs) :
    (packedRowOrigin F z P hb hf fit rel x).cell=
      declaredCell N P.rowLabel P.colLabel (actualEdgeOfItem F z q fit perm x) := by
  let R := packedRowOrigin F z P hb hf fit rel x
  let e := actualEdgeOfItem F z q fit perm x
  have K := R.rawCell
  rw [actual_item_tag F z q fit perm x,graphWord_cell] at K
  apply wordCell_injective a
  change wordCell R.cell=_
  rw [←Option.some.inj K,codePair,sourceCell,hf,hf,hrow,hcol,
    ←labels (.inl (N.row e)),←labels (.inr (N.col e))]
  rfl

noncomputable def installedChart : PhysicalPacking N a (Fin 64) where
  rowLabel := P.rowLabel
  colLabel := P.colLabel
  copies := P.copies
  mask := childMask a P.copies
  seat := (actualEdgeOfItem F z q fit perm).symm.toEmbedding.trans
    ⟨fun x=>stableItem ha (packedRowOrigin F z P hb hf fit rel x),
     stable_row_address_inj F z P hb hf ha fit rel perm⟩
  exactCell e := by
    let x := (actualEdgeOfItem F z q fit perm).symm e
    change physicalCell (childMask a P.copies)
      (stableItem ha (packedRowOrigin F z P hb hf fit rel x))=_
    rw [stable_item_cell,stable_row_ordered_cell F z P hrow hcol hb hf labels fit rel perm]
    rw [show actualEdgeOfItem F z q fit perm x=e from (actualEdgeOfItem F z q fit perm).apply_symm_apply e]
  paddedBudget := P.paddedBudget

noncomputable def installedEdgeOrder : List E :=
  (seatedItems xs).attach.map (actualEdgeOfItem F z q fit perm)

theorem installed_edge_order_exact :
    (installedEdgeOrder F z fit perm).Nodup ∧ ∀ e,e∈installedEdgeOrder F z fit perm := by
  have td : ((seatedItems xs).map (fun r=>r.2.tag)).Nodup := by
    rw [seated_items_tags,perm.nodup_iff,source_tag_tape]
    exact List.nodup_ofFn.mpr (ordinal_tag_injective F z q fit)
  have nd := List.Nodup.of_map _ td
  constructor
  · exact nd.attach.map (actualEdgeOfItem F z q fit perm).injective
  · intro e
    unfold installedEdgeOrder
    exact List.mem_map.mpr ⟨(actualEdgeOfItem F z q fit perm).symm e,List.mem_attach _ _,
      (actualEdgeOfItem F z q fit perm).apply_symm_apply e⟩

theorem install_full_greedy_seat_table (i : Fin a) (axis : List Bool) (clock : axis.length=i.val) :
    let Q := installedChart F z P hrow hcol hb hf labels ha fit rel perm
    let order := installedEdgeOrder F z fit perm
    let W := writeSeatedBoxes a (q-a) axis xs
    W.result=order.map (physicalSeatField Q i (childPageKey (q-a))) ∧
      W.steps≤(2*maskedSeatFee a (q-a)+12)*Fintype.card E+5*(2^(6*a)*2^(6*a)) := by
  let Q := installedChart F z P hrow hcol hb hf labels ha fit rel perm
  obtain ⟨_,_,_,_,boxes,_,rows⟩ := packed_header_lift F hb z rel
  obtain ⟨Wv,Wc⟩ := write_seated_boxes_exact a (q-a) axis xs (fun x hx=>
    (item_seat_write_from_origin ha (packedRowOrigin F z P hb hf fit rel ⟨x,hx⟩) i axis clock).2)
  rw [boxes,rows] at Wc
  refine ⟨Wv.trans ?_,Wc⟩
  unfold installedEdgeOrder
  rw [List.map_map]
  rw [←List.attach_map_val (l:=seatedItems xs) (f:=seatOutput (a:=a) (w:=q-a) axis)]
  apply List.map_congr_left
  intro x _
  let V := packedRowOrigin F z P hb hf fit rel x
  let ed := actualEdgeOfItem F z q fit perm x
  let st := stableItem ha V
  have eQ : Q.seat ed = st := by
    change stableItem ha (packedRowOrigin F z P hb hf fit rel
      ((actualEdgeOfItem F z q fit perm).symm ed)) = _
    rw [show (actualEdgeOfItem F z q fit perm).symm ed=x from
      (actualEdgeOfItem F z q fit perm).symm_apply_apply x]
  have rv := (item_seat_write_from_origin ha V i axis clock).1
  change seatOutput axis x.val=physicalSeatField Q i (childPageKey (q-a)) ed
  rw [show seatOutput axis x.val=_ from rv]
  unfold physicalSeatField slotWord
  rw [eQ]
  have v := stable_item_cell ha V
  change SeatField.mk (childPageKey _ st.1) (word st.2.val) (word (V.cell i).1.val)
    (word (V.cell i).2.val)=
    ⟨childPageKey _ st.1,word st.2.val,
      word ((physicalCell (childMask a P.copies) st i).1.val),
      word ((physicalCell (childMask a P.copies) st i).2.val)⟩
  rw [v]
end Exact

#print axioms write_seated_boxes_exact
#print axioms stable_row_address_inj
#print axioms stable_row_ordered_cell
#print axioms installed_edge_order_exact
#print axioms install_full_greedy_seat_table
end J6R32ChildResidentTransfer