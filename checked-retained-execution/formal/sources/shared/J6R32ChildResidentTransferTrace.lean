import J6R32ChildResidentTransferSeat
import J6R14LayoutCostGreedy
import J6R14LayoutCostStable

/-! Recover the actual ordered-cell and within-cell rank of every *real*
record in the paid R14 output. No empty padded slot becomes an edge. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open P11FullPacking J6R14LayoutCost J6R24LegalLayout J6R27OriginalGate J6R15ModeCost
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource J6R11CollisionReindex
set_option maxHeartbeats 13000000

abbrev SeatedItem := ExportBox×Seated

def seatedItems (xs : List ExportBox) : List SeatedItem :=
  xs.flatMap fun box=>box.rows.map fun row=>(box,row)

theorem seated_items_tags (xs : List ExportBox) :
    (seatedItems xs).map (fun r=>r.2.tag) = xs.flatMap (fun x=>x.rows.map Seated.tag) := by
  unfold seatedItems
  rw [List.map_flatMap]
  congr 1
  funext x
  rw [List.map_map]
  rfl

theorem seated_item_mem {xs : List ExportBox} {p : SeatedItem} (h : p∈seatedItems xs) :
    p.1∈xs ∧ p.2∈p.1.rows := by
  obtain ⟨box,b,z⟩ := List.mem_flatMap.mp h
  obtain ⟨row,m,eq⟩ := List.mem_map.mp z
  cases eq
  exact ⟨b,m⟩

private theorem box_match {a b q : ℕ} {bs : List (Box Tagged)} {xs : List ExportBox}
    (h : List.Forall₂ (boxFaithful a b q) bs xs) (x : ExportBox) (hx : x∈xs) :
    ∃ B∈bs,boxFaithful a b q B x := by
  induction h with
  | nil => simp at hx
  | @cons B X ms ns H Hs ih =>
    rcases List.mem_cons.mp hx with e|e
    · subst X
      exact ⟨B,List.mem_cons_self,H⟩
    · obtain ⟨C,Cs,Hp⟩ := ih e
      exact ⟨C,List.mem_cons_of_mem _ Cs,Hp⟩

structure SeatedOrigin (a b q : ℕ) (bs : List (Box Tagged)) (x : SeatedItem) where
  source : Box Tagged
  present : source∈bs
  cell : Cell (Fin a) (Fin 64)
  pos : Fin source.rows.length
  header : source.key=wordCell cell
  key : x.1.key=wordCell cell
  axes : x.1.axes=axesOf cell
  flags : x.1.flags=marksOf cell
  tag : x.2.tag=source.rows[pos]
  rawCell : J6R14LayoutCost.rawCell x.2.tag.edge=some (wordCell cell)
  rawSeat : x.2.address=(seatWords (marksOf cell) (encodeBits q pos.val)).result
  pageFits : bitsValue x.2.address.page<b
  width : pos.val<2^q

theorem seated_item_origin {a b q : ℕ} {bs : List (Box Tagged)} {xs : List ExportBox}
    (h : List.Forall₂ (boxFaithful a b q) bs xs)
    (fit : ∀ B∈bs,B.rows.length<2^q)
    (x : SeatedItem) (hx : x∈seatedItems xs) : Nonempty (SeatedOrigin a b q bs x) := by
  obtain ⟨hx1,hx2⟩ := seated_item_mem hx
  obtain ⟨B,hB,hK,tags,c,hc,ax,hs,H⟩ := box_match h x.1 hx1
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hx2
  have lengths : x.1.rows.length=B.rows.length := by
    have Q := congrArg List.length tags
    rwa [List.length_map] at Q
  let k : Fin B.rows.length := ⟨j.val,j.isLt.trans_eq lengths⟩
  obtain ⟨t,hT,hTag,hRaw,hAddr,hPg,_⟩ := H k
  have ht : x.2=t := by
    have r : x.1.rows[j.val]?=some x.2 := by
      rw [List.getElem?_eq_getElem j.isLt]
      exact congrArg some hj
    rw [r] at hT
    exact Option.some.inj hT
  rw [←ht] at hTag hRaw hAddr hPg
  exact ⟨⟨B,hB,c,k,hc,hK.trans hc,ax,hs,hTag,hc ▸ hRaw,hAddr,hPg,k.isLt.trans (fit _ hB)⟩⟩

def itemAnchor (x : SeatedItem) : AnchorWord :=
  ⟨x.1.key,[],⟨x.1.axes,x.1.flags,x.2.address⟩⟩

theorem origin_rank_fits {a b q : ℕ} {bs : List (Box Tagged)} {x : SeatedItem}
    (hA : a≤q) (O : SeatedOrigin a b q bs x) :
    O.pos.val<min (2^q) (b*2^a) := by
  refine lt_min O.width ?_
  have hp := O.pageFits
  rw [O.rawSeat,(seatWords_exact (marksOf O.cell) (encodeBits q O.pos.val)
    (by rwa [marksOf_len,encodeBits_length])).2.2.2.2.1,
    drop_value,marksOf_len,encodeBits_exact _ _ O.width] at hp
  exact (Nat.div_lt_iff_lt_mul (by positivity)).mp hp

noncomputable def stableItem {a b q : ℕ} {bs : List (Box Tagged)} {x : SeatedItem}
    (hA : a≤q) (O : SeatedOrigin a b q bs x) : Physical a b (Fin 64) :=
  twistSeat (childMask a b) (stableAddr hA (O.cell,⟨O.pos.val,origin_rank_fits hA O⟩))

theorem stable_item_cell {a b q : ℕ} {bs : List (Box Tagged)} {x : SeatedItem}
    (hA : a≤q) (O : SeatedOrigin a b q bs x) :
    physicalCell (childMask a b) (stableItem hA O)=O.cell := by
  unfold stableItem
  rw [twist_preserves_ordered_cell,stableAddr_cell]

private theorem decode_same {a b : ℕ} (c : Cell (Fin a) (Fin 64))
    {x y : SeatWords} (e : x=y) (hx : bitsValue x.page<b) (hy : bitsValue y.page<b) :
    decodePhysical c x hx=decodePhysical c y hy := by
  cases e
  rfl

theorem item_seat_write_from_origin {a b q : ℕ} {bs : List (Box Tagged)} {x : SeatedItem}
    (hA : a≤q) (O : SeatedOrigin a b q bs x) (i : Fin a) (axis : List Bool) (clk : axis.length=i.val) :
    let z := stableItem hA O
    let out := writeMaskedSeat a (q-a) axis (itemAnchor x)
    out.result=⟨childPageKey (q-a) z.1,word z.2.val,word ((O.cell i).1.val),word ((O.cell i).2.val)⟩ ∧
      out.steps≤maskedSeatFee a (q-a) := by
  have e := seatWords_exact (marksOf O.cell) (encodeBits q O.pos.val)
    (by rwa [marksOf_len,encodeBits_length])
  have slotL : x.2.address.slot.length=a := by rw [O.rawSeat,e.1,marksOf_len]
  have selL : x.2.address.selector.length=a := by rw [O.rawSeat,e.2.1,marksOf_len]
  have pageL : x.2.address.page.length=q-a := by
    rw [O.rawSeat,e.2.2.2.2.1,List.length_drop,marksOf_len,encodeBits_length]
  obtain ⟨eq,bill⟩ := raw_masked_seat_exact i axis clk O.cell (itemAnchor x)
    O.key O.axes slotL selL pageL O.pageFits
  have st :
      twistSeat (childMask a b) (decodePhysical O.cell x.2.address O.pageFits)=stableItem hA O := by
    unfold stableItem stableAddr
    congr 1
    change decodePhysical O.cell x.2.address O.pageFits=
      decodePhysical O.cell (seatWords (marksOf O.cell) (encodeBits q O.pos.val)).result _
    exact decode_same O.cell O.rawSeat _ _
  change (writeMaskedSeat a (q-a) axis (itemAnchor x)).result=_ ∧ _
  change (writeMaskedSeat a (q-a) axis (itemAnchor x)).result=
    ⟨childPageKey (q-a) (twistSeat (childMask a b) (decodePhysical O.cell x.2.address O.pageFits)).1,
      word (twistSeat (childMask a b) (decodePhysical O.cell x.2.address O.pageFits)).2.val,
      _,_⟩ at eq
  rw [st] at eq
  exact ⟨eq,bill⟩

#print axioms seated_items_tags
#print axioms seated_item_origin
#print axioms origin_rank_fits
#print axioms stable_item_cell
#print axioms item_seat_write_from_origin
end J6R32ChildResidentTransfer