import J6R75RawPeakLayoutWords

/-! Exact source raw ExportBox fields after actual packet serialization,
including the emitted axes, flags, tag, slot, selector and page words.
No inference about packing order is made from output sizes alone. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R14LayoutCost
open J6R12CollisionMenu J6R17ModeTape P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11700000
set_option maxRecDepth 4150
set_option Elab.async false

theorem literal_layout_seat_has_exact_bit_width (a q : ℕ)
    (marks : AxisMarks) (rank : List Bool) (hm : marks.length=a) (hr : rank.length=q)
    (fits : a≤q) :
    rawAddressLayoutBits (seatWords marks rank).result=a+q := by
  have h : marks.length≤rank.length := by rwa [hm,hr]
  obtain ⟨first,second,_,_,pg,_⟩ := seatWords_exact marks rank h
  unfold rawAddressLayoutBits
  rw [first,second,pg,List.length_drop,hm,hr]
  omega

private theorem source_axis_words_have_exact_bits {a : ℕ} (c : Cell (Fin a) (Fin 64)) :
    rawLayoutBits rawAxisLayoutBits (axesOf c)=14*a := by
  have w (x : AxisWord) (mem : x∈axesOf c) : rawAxisLayoutBits x=14 := by
    rw [axesOf,List.mem_ofFn] at mem
    obtain ⟨i,rfl⟩ := mem
    unfold rawAxisLayoutBits axisSpec
    simp [symbol_length]
  rw [raw_layout_bits_fixed _ _ _ w]
  simp [axesOf]

theorem faithful_export_box_bit_width {a pages q : ℕ} (B : Box Tagged) (X : ExportBox)
    (faithful : boxFaithful a pages q B X) (fits : a≤q)
    (b w : ℕ) (key : rawCellLayoutBits B.key=2*b)
    (tags : ∀ t∈B.rows,rawTaggedLayoutBits t=w) :
    rawExportLayoutBits X=(2*b+16*a)+(w+(a+q))*X.rows.length := by
  obtain ⟨same,sharing,c,raw,axes,flags,each⟩ := faithful
  have len : X.rows.length=B.rows.length := by
    simpa only [List.length_map] using congrArg List.length sharing
  have widths (t : Seated) (hit : t∈X.rows) : rawSeatedLayoutBits t=w+(a+q) := by
    obtain ⟨i,placed⟩ := List.mem_iff_get.mp hit
    let j : Fin B.rows.length := Fin.cast len i
    obtain ⟨s,atSlot,tag,_,physical,_⟩ := each j
    change X.rows[i.val]?=some s at atSlot
    have located : X.rows[i.val]?=some t := by
      rw [List.getElem?_eq_getElem i.isLt]
      exact congrArg some placed
    have eq : t=s := Option.some.inj (located.symm.trans atSlot)
    rw [eq]
    have tagWidth : rawTaggedLayoutBits s.tag=w := by
      rw [tag]
      exact tags _ (List.getElem_mem j.isLt)
    unfold rawSeatedLayoutBits
    rw [tagWidth,physical,literal_layout_seat_has_exact_bit_width a q
      (marksOf c) (encodeBits q j.val) (marksOf_len c) (encodeBits_length _ _) fits]
  unfold rawExportLayoutBits
  rw [same,key,axes,source_axis_words_have_exact_bits,flags,marksOf_len,
    raw_layout_bits_fixed _ _ _ widths]
  omega

theorem faithful_export_layout_tape_bits {a pages q : ℕ}
    (B : List (Box Tagged)) (X : List ExportBox)
    (faithful : List.Forall₂ (boxFaithful a pages q) B X) (fits : a≤q)
    (b w : ℕ) (keys : ∀ box∈B,rawCellLayoutBits box.key=2*b)
    (tags : ∀ box∈B,∀ t∈box.rows,rawTaggedLayoutBits t=w) :
    rawLayoutBits rawExportLayoutBits X=(2*b+16*a)*X.length+(w+(a+q))*exportRows X := by
  induction faithful with
  | nil=>simp [rawLayoutBits,exportRows]
  | @cons h x hs xs f fs ih=>
    have this := faithful_export_box_bit_width h x f fits b w (keys h List.mem_cons_self)
      (tags h List.mem_cons_self)
    have next := ih (fun u hu=>keys u (List.mem_cons_of_mem _ hu))
      (fun u hu=>tags u (List.mem_cons_of_mem _ hu))
    change rawExportLayoutBits x+rawLayoutBits rawExportLayoutBits xs=
      (2*b+16*a)*(xs.length+1)+(w+(a+q))*exportRows (x::xs)
    have rowCount : exportRows (x::xs)=x.rows.length+exportRows xs := by simp [exportRows]
    rw [this,next,rowCount,Nat.mul_succ,Nat.mul_add]
    omega

section Source
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)

theorem actual_fixed_export_writes_exactly_the_source_payload
    (alphabet : F.b=6*a) (labels : ∀ u,F.label u=coordinateLabel u)
    (q : ℕ) (hq : 0<q) (fits : a≤q) (words : Fintype.card E<2^q) :
    let p := packFixed F.kR F.kC F.b q a (F.graph (fun x=>some (z x)))
    rawLayoutBits rawExportLayoutBits p.result.boxes=
      (2*F.b+16*a)*(2^F.b*2^F.b)+
        ((q+fullEdgeLayoutWidth F.kR F.kC F.b)+(a+q))*Fintype.card E ∧
    p.result.copies.length=q+1 := by
  let p := packFixed F.kR F.kC F.b q a (F.graph (fun x=>some (z x)))
  obtain ⟨copy,_,faithful,_,_⟩ := packFixed_exact F alphabet labels z q hq fits words
  have key (B : Box Tagged) (hit : B∈sourceBoxes F z q) : rawCellLayoutBits B.key=2*F.b := by
    obtain ⟨k,found,rfl⟩ := List.mem_map.mp hit
    obtain ⟨l,r⟩ := (allPairs_mem F.b k).mp found
    change k.1.length+k.2.length=2*F.b
    rw [l,r]
    omega
  have tag (B : Box Tagged) (hit : B∈sourceBoxes F z q) (t : Tagged) (hm : t∈B.rows) :
      rawTaggedLayoutBits t=q+fullEdgeLayoutWidth F.kR F.kC F.b := by
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hit
    exact source_tag_width_of_real_occurrence F z q t (List.mem_filter.mp hm).1
  have width := faithful_export_layout_tape_bits _ p.result.boxes faithful fits _ _ key tag
  obtain ⟨_,_,_,_,count,_,edges⟩ := packed_header_lift F alphabet z faithful
  have c : p.result.boxes.length=2^F.b*2^F.b := count.trans (by rw [alphabet])
  exact ⟨width.trans (by rw [c,edges]),copy⟩
end Source

#print axioms literal_layout_seat_has_exact_bit_width
#print axioms faithful_export_box_bit_width
#print axioms actual_fixed_export_writes_exactly_the_source_payload
end J6R75RawPeak
