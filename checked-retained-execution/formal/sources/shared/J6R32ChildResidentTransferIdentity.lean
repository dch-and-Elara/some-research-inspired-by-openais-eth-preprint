import J6R32ChildResidentTransferTrace

/-! The serial attached before sorting certifies which exact child edge
occupies each retained row. Parallel edges share cells but not ordinals. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open P11FullPacking J6R14LayoutCost J6R24LegalLayout J6R27OriginalGate J6R15ModeCost
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource J6R11CollisionReindex
set_option maxHeartbeats 12500000

theorem tags_in_enumeration_order (q : ℕ) (xs : List EdgeTape) :
    tagSpec q 0 xs=List.ofFn (fun j : Fin xs.length=>⟨encodeBits q j.val,xs.get j⟩) := by
  apply List.ext_getElem?
  intro i
  rw [tagSpec_at,List.getElem?_ofFn,zero_add]
  by_cases hi : i<xs.length
  · rw [List.getElem?_eq_getElem hi,dif_pos hi]
    rfl
  · rw [List.getElem?_eq_none (Nat.le_of_not_gt hi),dif_neg hi]
    rfl

section Chart
variable {E R C : Type} [Fintype E] {a : ℕ}
variable (F : Format E R C (Fin a→Fin 64)) (z : R⊕C→Fin a→Fin 64)
variable (q : ℕ) (hfit : Fintype.card E<2^q)

def ordinalTag (j : Fin F.edges.length) : Tagged :=
  ⟨encodeBits q j.val,graphWord F z (F.edges.get j)⟩

theorem source_tag_tape :
    tagSpec q 0 (F.graph (fun v=>some (z v)))=
      List.ofFn (ordinalTag F z q) := by
  have h : F.graph (fun v=>some (z v))=F.edges.map (graphWord F z) := rfl
  rw [h,tags_in_enumeration_order]
  apply List.ext_getElem? 
  intro j
  rw [List.getElem?_ofFn,List.getElem?_ofFn]
  by_cases hj : j<F.edges.length
  · have hj' : j<(F.edges.map (graphWord F z)).length := by rwa [List.length_map]
    rw [dif_pos hj',dif_pos hj]
    simp only [ordinalTag,List.get_eq_getElem,List.getElem_map]
  · have hj' : ¬j<(F.edges.map (graphWord F z)).length := by rwa [List.length_map]
    rw [dif_neg hj',dif_neg hj]

include hfit in
theorem ordinal_tag_injective : Function.Injective (ordinalTag F z q) := by
  intro x y h
  have he := congrArg (fun t : Tagged=>bitsValue t.serial) h
  change bitsValue (encodeBits q x.val)=bitsValue (encodeBits q y.val) at he
  rw [encodeBits_exact _ _ (x.isLt.trans (F.graphEdges.trans_lt hfit)),
    encodeBits_exact _ _ (y.isLt.trans (F.graphEdges.trans_lt hfit))] at he
  exact Fin.ext he

variable {xs : List ExportBox}
variable (perm : (xs.flatMap (fun x=>x.rows.map Seated.tag)).Perm
  (tagSpec q 0 (F.graph (fun v=>some (z v)))))
abbrev Observed (xs : List ExportBox) := {x : SeatedItem // x∈seatedItems xs}

include perm in
theorem each_item_has_ordinal (x : Observed xs) :
    ∃ j,x.val.2.tag=ordinalTag F z q j := by
  have hit : x.val.2.tag∈(seatedItems xs).map (fun r=>r.2.tag) :=
    List.mem_map.mpr ⟨x.val,x.property,rfl⟩
  rw [seated_items_tags] at hit
  have src := perm.mem_iff.mp hit
  rw [source_tag_tape] at src
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp src
  exact ⟨j,hj.symm⟩

noncomputable def itemOrdinal (x : Observed xs) : Fin F.edges.length :=
  (each_item_has_ordinal F z q perm x).choose

theorem item_ordinal_exact (x : Observed xs) :
    x.val.2.tag=ordinalTag F z q (itemOrdinal F z q perm x) :=
  (each_item_has_ordinal F z q perm x).choose_spec

include hfit in
theorem item_ordinals_bijective :
    Function.Bijective (itemOrdinal F z q perm) := by
  have hUni : (List.ofFn (ordinalTag F z q)).Nodup :=
    List.nodup_ofFn.mpr (ordinal_tag_injective F z q hfit)
  have hd : ((seatedItems xs).map (fun r=>r.2.tag)).Nodup := by
    rw [seated_items_tags,perm.nodup_iff,source_tag_tape]
    exact hUni
  constructor
  · intro x y eq
    apply Subtype.ext
    apply List.inj_on_of_nodup_map hd x.property y.property
    rw [item_ordinal_exact F z q perm x,item_ordinal_exact F z q perm y,eq]
  · intro j
    have jtag : ordinalTag F z q j ∈ (seatedItems xs).map (fun r=>r.2.tag) := by
      rw [seated_items_tags,perm.mem_iff,source_tag_tape]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    obtain ⟨x,hx,h⟩ := List.mem_map.mp jtag
    let y : Observed xs := ⟨x,hx⟩
    exact ⟨y,ordinal_tag_injective F z q hfit ((item_ordinal_exact F z q perm y).symm.trans h)⟩

noncomputable def actualEdgeOfItem : Observed xs ≃ E :=
  (Equiv.ofBijective (itemOrdinal F z q perm) (item_ordinals_bijective F z q hfit perm)).trans
    (Equiv.ofBijective F.edges.get ⟨fun _ _ eq=>F.edgesNodup.get_inj_iff.mp eq,
      fun e=>List.mem_iff_get.mp (F.edgesAll e)⟩)

theorem actual_item_tag (x : Observed xs) :
    x.val.2.tag.edge = graphWord F z (actualEdgeOfItem F z q hfit perm x) :=
  congrArg Tagged.edge (item_ordinal_exact F z q perm x)

theorem source_box_determined_by_key {X Y : Box Tagged}
    (hx : X∈sourceBoxes F z q) (hy : Y∈sourceBoxes F z q) (h : X.key=Y.key) : X=Y := by
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hy
  change k=l at h
  rw [h]

theorem same_stable_seat_same_tag {b : ℕ} {x y : SeatedItem} (hA : a≤q)
    (O : SeatedOrigin a b q (sourceBoxes F z q) x)
    (Q : SeatedOrigin a b q (sourceBoxes F z q) y)
    (eq : stableItem hA O=stableItem hA Q) : x.2.tag=y.2.tag := by
  have he : ((O.cell,⟨O.pos.val,origin_rank_fits hA O⟩) : AddressRank a b q) =
      (Q.cell,⟨Q.pos.val,origin_rank_fits hA Q⟩) :=
    stableAddr_injective hA ((twistChart (childMask a b)).injective eq)
  have hCell := congrArg Prod.fst he
  have hr := congrArg (fun p : AddressRank a b q=>p.2.val) he
  have hBox := source_box_determined_by_key F z q O.present Q.present
    (O.header.trans ((congrArg wordCell hCell).trans Q.header.symm))
  have hTag : O.source.rows[O.pos.val]?=Q.source.rows[Q.pos.val]? := by
    exact congrArg₂ (fun (xs : List Tagged) (i : ℕ)=>xs[i]?) (congrArg Box.rows hBox) hr
  rw [List.getElem?_eq_getElem O.pos.isLt,List.getElem?_eq_getElem Q.pos.isLt] at hTag
  exact O.tag.trans ((Option.some.inj hTag).trans Q.tag.symm)
end Chart

#print axioms tags_in_enumeration_order
#print axioms source_tag_tape
#print axioms item_ordinals_bijective
#print axioms actual_item_tag
#print axioms same_stable_seat_same_tag
end J6R32ChildResidentTransfer