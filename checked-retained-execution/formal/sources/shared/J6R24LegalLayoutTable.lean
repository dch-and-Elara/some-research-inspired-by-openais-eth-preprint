
import J6R24LegalLayoutStable
import J6R24LegalLayoutRange

/-! The real executable's emitted rows enumerate the occupied legal
wires exactly once. The inverse of the typed equivalence is used only
to name each physically emitted record in the proof. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open P11FullPacking J6OrientedHost J6R14LayoutCost J6R23PaddingCensus
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionEdges
set_option maxHeartbeats 15500000
set_option linter.unusedSectionVars false

abbrev AttachedKey (a : ℕ) := {k : CellWord // k∈allPairs (6*a)}

noncomputable def typedKey (a : ℕ) (k : AttachedKey a) : CellType a :=
  (tokenChart a).symm ⟨k.val,List.mem_toFinset.mpr k.property⟩

theorem typed_key_word (a : ℕ) (k : AttachedKey a) : wordCell (typedKey a k)=k.val :=
  congrArg Subtype.val ((tokenChart a).apply_symm_apply _)

theorem typed_key_injective (a : ℕ) : Function.Injective (typedKey a) := by
  intro k₁ k₂ h
  exact Subtype.ext ((typed_key_word a k₁).symm.trans ((congrArg wordCell h).trans (typed_key_word a k₂)))

noncomputable def typedCells (a : ℕ) : List (CellType a) :=
  (allPairs (6*a)).attach.map (typedKey a)

theorem typed_cells_exact (a : ℕ) :
    (typedCells a).Nodup ∧ (∀ c : CellType a,c∈typedCells a) ∧
      (typedCells a).map wordCell=allPairs (6*a) := by
  have H : (allPairs (6*a)).attach.Nodup := (allPairs_nodup (6*a)).attach
  constructor
  · exact H.map (typed_key_injective a)
  constructor
  · intro c
    let k : AttachedKey a := ⟨wordCell c,List.mem_toFinset.mp (encodeToken a c).property⟩
    apply List.mem_map.mpr
    exact ⟨k,List.mem_attach _ _,word_cell_injective a (typed_key_word a k)⟩
  · rw [typedCells,List.map_map]
    calc
      _ = (allPairs (6*a)).attach.map Subtype.val := by
        apply List.map_congr_left
        intro k _
        exact typed_key_word a k
      _ = _ := List.attach_map_subtype_val _

noncomputable def fullRankOrder (a b : ℕ) : List (FullRank a b) :=
  (typedCells a).product (List.finRange (b*2^a))

theorem full_rank_order_exact (a b : ℕ) :
    (fullRankOrder a b).Nodup ∧ (∀ x : FullRank a b,x∈fullRankOrder a b) := by
  refine ⟨(typed_cells_exact a).1.product (List.nodup_finRange _),?_⟩
  intro x
  exact List.mem_product.mpr ⟨(typed_cells_exact a).2.1 x.1,List.mem_finRange x.2⟩

def anchorAt {a b : ℕ} (q : ℕ) (x : FullRank a b) : AnchorWord :=
  expectedAnchor a q (wordCell x.1) x.2.val

theorem complete_tape_exact (a b q : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q) :
    (allSeatWords a b q).result=(fullRankOrder a b).map (anchorAt q) ∧
      (allSeatWords a b q).steps≤completeSeatFee a b q := by
  obtain ⟨form,bill⟩ := all_seat_words_exact a b q hq ha cap
  refine ⟨?_,bill⟩
  rw [form,←(typed_cells_exact a).2.2]
  unfold fullRankOrder
  simp only [List.flatMap_map,List.product,List.map_flatMap,List.map_map]
  apply congrArg (fun f : CellType a→List AnchorWord=>(typedCells a).flatMap f)
  funext c
  rw [outRows,List.ofFn_eq_map]
  rfl

theorem anchor_decodes {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q) (x : FullRank a b) :
    let t := anchorAt q x
    ∃ hp : bitsValue t.physical.seat.page<b,
      decodePhysical x.1 t.physical.seat hp=fullStable ha cap x := by
  let r := encodeBits q x.2.val
  let X := exportOne a (wordCell x.1) r
  have geom : X.result.seat=(seatWords (marksOf x.1) r).result := by
    change (seatWords (prepareHeader a (wordCell x.1)).result.2 r).result=_
    rw [(prepareHeader_exact x.1).1]
  have W : a≤r.length := by simpa only [r,encodeBits_length] using ha
  have t : bitsValue r<b*2^a := by
    change bitsValue (encodeBits q x.2.val)<_
    rw [encodeBits_exact _ _ (x.2.isLt.trans_le cap)]
    exact x.2.isLt
  have hp := page_in_range (marksOf x.1) r (by rwa [marksOf_len]) b (by rwa [marksOf_len])
  have hq : bitsValue X.result.seat.page<b := by rwa [geom]
  refine ⟨hq,?_⟩
  have h0 :
      decodePhysical x.1 X.result.seat hq =
        decodePhysical x.1 (seatWords (marksOf x.1) r).result hp := by
    simp only [geom]
  exact h0

noncomputable def orderedWires {a b m l : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    List (Wire w m b l) :=
  (fullRankOrder a b).map (placedRank w hm hL).symm

theorem ordered_wires_exact {a b m l : ℕ} (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    (orderedWires w hm hL).Nodup ∧ (∀ e, e∈orderedWires w hm hL) := by
  obtain ⟨nd,all⟩ := full_rank_order_exact a b
  refine ⟨nd.map (placedRank w hm hL).symm.injective,fun e=>List.mem_map.mpr ?_⟩
  exact ⟨placedRank w hm hL e,all _,(placedRank w hm hL).symm_apply_apply e⟩

theorem actual_legal_chart_tape {a b m l q : ℕ} (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (w : Fin a→Fin 64) (hm : m≤b) (hL : 2*l=2^a) :
    let C := deterministicLegal ha cap.le w hm hL
    let seq := orderedWires w hm hL
    let run := allSeatWords a b q
    seq.Nodup ∧ (∀ e,e∈seq) ∧ run.result=seq.map (fun e=>anchorAt q (placedRank w hm hL e)) ∧
    (∀ e, let x := placedRank w hm hL e
      let record := anchorAt q x
      ∃ hp : bitsValue record.physical.seat.page<b,
        decodePhysical x.1 record.physical.seat hp=C.seats e) ∧
    run.steps≤completeSeatFee a b q := by
  obtain ⟨nd,all⟩ := ordered_wires_exact w hm hL
  obtain ⟨r,cost⟩ := complete_tape_exact a b q hq ha cap
  refine ⟨nd,all,?_,?_,cost⟩
  · rw [r,orderedWires,List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  · intro e
    exact anchor_decodes ha cap.le (placedRank w hm hL e)

#print axioms typed_cells_exact
#print axioms full_rank_order_exact
#print axioms complete_tape_exact
#print axioms anchor_decodes
#print axioms ordered_wires_exact
#print axioms actual_legal_chart_tape
end J6R24LegalLayout
