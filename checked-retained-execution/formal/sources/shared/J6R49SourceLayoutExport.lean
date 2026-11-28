import J6R49SourceLayoutOrder

/-! Same installed R32 chart: the serial attached by the actual greedy
program identifies the precise pre-sort edge. The proof-side
equivalence verifies the byte program; it is not a lookup algorithm. -/
namespace J6R49SourceLayout
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R14LayoutCost J6R27OriginalGate J6R31RootResidentTables P11FullPacking
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionMenu J6R17ModeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R10Repack J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6300000
set_option maxRecDepth 2400
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

theorem seated_items_length (xs : List ExportBox) : (seatedItems xs).length=exportRows xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((x.rows.map (fun y=>(x,y)))++seatedItems xs).length=_
    rw [List.length_append,List.length_map,ih]
    simp [exportRows]

variable {E R C : Type} [Fintype E] {a q : ℕ}
variable (F : Format E R C (Fin a→Fin 64))
variable (fit : Fintype.card E<2^q)

def sourceIndex : Fin F.edges.length≃E :=
  rosterIndex F.edges F.edgesNodup F.edgesAll

def sourceKey (e : E) : Word q := word ((sourceIndex F).symm e).val

include fit in
theorem source_serial_key_injective : Function.Injective (sourceKey (q:=q) F) := by
  intro x y h
  have vx : ((sourceIndex F).symm x).val<2^q :=
    ((sourceIndex F).symm x).isLt.trans (F.graphEdges.trans_lt fit)
  have vy : ((sourceIndex F).symm y).val<2^q :=
    ((sourceIndex F).symm y).isLt.trans (F.graphEdges.trans_lt fit)
  apply (sourceIndex F).symm.injective
  apply Fin.ext
  have h' := congrArg Word.val h
  change (word (q:=q) ((sourceIndex F).symm x).val).val =
    (word (q:=q) ((sourceIndex F).symm y).val).val at h'
  rwa [word_val vx,word_val vy] at h'

variable (z : R⊕C→Fin a→Fin 64)
variable {boxes : List ExportBox}
variable (perm : (boxes.flatMap (fun x=>x.rows.map Seated.tag)).Perm
  (tagSpec q 0 (F.graph (fun v=>some (z v)))))

theorem item_source_ordinal (x : Observed boxes) :
    (sourceIndex F).symm (actualEdgeOfItem F z q fit perm x)=itemOrdinal F z q perm x := by
  apply (sourceIndex F).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem actual_item_serial (x : Observed boxes) :
    (fitWord q x.val.2.tag.serial).result=sourceKey (q:=q) F (actualEdgeOfItem F z q fit perm x) := by
  have ts := congrArg Tagged.serial (item_ordinal_exact F z q perm x)
  change x.val.2.tag.serial=encodeBits q (itemOrdinal F z q perm x).val at ts
  apply word_bits_inj
  have width : x.val.2.tag.serial.length=q := by rw [ts,encodeBits_length]
  rw [fit_word_value q _ width]
  unfold sourceKey
  rw [item_source_ordinal]
  exact ts

theorem packed_keys_are_the_source_serials :
    (packedSerials q boxes).result=(installedEdgeOrder F z fit perm).map (sourceKey F) := by
  rw [packed_serials_exact]
  change (seatedItems boxes).map (fun x=>(fitWord q x.2.tag.serial).result)=_
  unfold installedEdgeOrder
  rw [List.map_map,←List.attach_map_val (l:=seatedItems boxes)
    (f:=fun x=>(fitWord q x.2.tag.serial).result)]
  apply List.map_congr_left
  intro x _
  exact actual_item_serial F fit z perm x

include fit in
theorem source_order_uses_finite_ordinal_words {A : Type*} (stride : ℕ) (raw : List A)
    (pos : 0<q) (sameLength : raw.length=F.edges.length) :
    ordinalWords q stride raw=
      ⟨F.edges.map (sourceKey F),6+q+(18*q+stride+8)*F.edges.length⟩ := by
  have hfit : raw.length<2^q := sameLength.trans_lt (F.graphEdges.trans_lt fit)
  rw [ordinal_words_exact q stride raw pos hfit]
  rw [sameLength]
  have h : List.ofFn (sourceIndex F) = F.edges := List.ofFn_get _
  have aux := congrArg (List.map (sourceKey (q:=q) F)) h
  rw [List.map_ofFn] at aux
  change (List.ofFn (fun x=>word (q:=q) (((sourceIndex F).symm ((sourceIndex F) x)).val)))=_ at aux
  simp only [Equiv.symm_apply_apply] at aux
  rw [aux]

/-- Join an actual paid resident result and the pre-sort tape. In the
descriptor implementation this tape is the selected raw edge stream. -/
def reorderInstalledSeats {A : Type*} {a k : ℕ} (q stride : ℕ)
    (boxes : List ExportBox) (seats : List (SeatField a k)) (raw : List A) :
    Meter (Option (List (SeatField a k))) :=
  let keys := ordinalWords q stride raw
  let joined := alignResidentSeats boxes seats keys.result
  ⟨joined.result,keys.steps+joined.steps+4⟩

section Installed
variable {N : Network E R C} (P : PhysicalPacking N a (Fin 64))
variable (hrow : F.row=N.row) (hcol : F.col=N.col)
variable (hb : F.b=6*a) (hf : ∀ x,F.label x=coordinateLabel x)
variable (labels : ∀ v,Sum.elim P.rowLabel P.colLabel v=z v)
variable (ha : a≤q)
variable (rel : List.Forall₂ (boxFaithful a P.copies q) (sourceBoxes F z q) boxes)
local notation "Q" => (installedChart F z P hrow hcol hb hf labels ha fit rel perm)

theorem exact_installed_export_in_source_order {A : Type*}
    (i : Fin a) (axis : List Bool) (clock : axis.length=i.val)
    (seats : List (SeatField a ((q-a)+13*a)))
    (written : seats=(writeSeatedBoxes a (q-a) axis boxes).result)
    (raw : List A) (sameLength : raw.length=F.edges.length) (stride : ℕ) (hq : 0<q) :
    let out := reorderInstalledSeats q stride boxes seats raw
    out.result=some (F.edges.map (physicalSeatField Q i (childPageKey (q-a)))) ∧
    out.steps≤6+q+(18*q+stride+8)*F.edges.length+
      alignFee q a ((q-a)+13*a) F.edges.length (exportRows boxes) boxes.length
        (packingTraffic boxes)+4 := by
  let place := installedEdgeOrder F z fit perm
  let key := sourceKey (q:=q) F
  let seat := physicalSeatField Q i (childPageKey (q-a))
  have L : place.length=exportRows boxes := by
    unfold place installedEdgeOrder
    rw [List.length_map,List.length_attach,seated_items_length]
  have S : seats=place.map seat :=
    written.trans (install_full_greedy_seat_table F z P hrow hcol hb hf labels ha fit rel perm i axis clock).1
  have K := packed_keys_are_the_source_serials F fit z perm
  have U := source_serial_key_injective F fit
  have all := (installed_edge_order_exact F z fit perm).2
  have H := align_resident_exact boxes seats place F.edges key seat K S L U (fun e _=>all e)
  have J := source_order_uses_finite_ordinal_words F fit stride raw hq sameLength
  unfold reorderInstalledSeats
  rw [J]
  refine ⟨H.1,?_⟩
  have fee := H.2
  change (alignResidentSeats boxes seats (F.edges.map key)).steps≤_ at fee
  rw [L] at fee
  change (6+q+(18*q+stride+8)*F.edges.length)+
    (alignResidentSeats boxes seats (F.edges.map key)).steps+4≤_
  omega

end Installed
#print axioms seated_items_length
#print axioms source_serial_key_injective
#print axioms item_source_ordinal
#print axioms actual_item_serial
#print axioms packed_keys_are_the_source_serials
#print axioms source_order_uses_finite_ordinal_words
#print axioms exact_installed_export_in_source_order
end
end J6R49SourceLayout