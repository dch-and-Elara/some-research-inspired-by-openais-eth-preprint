import J6R14LayoutCostExport
import J6R14LayoutCostRanks
import J6R14LayoutCostEnd

/-! A paid ordered-cell tape emits all retained incidence records with
their concrete packet selectors and bit addresses. Empty boxes only
emit their header; no padded fictitious edge is charged as a real one. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape P11FullPacking J6R12CollisionMenu

structure ExportBox where
  key : CellWord
  axes : List AxisWord
  flags : AxisMarks
  rows : List Seated

def exportBox (kR kC b q a : ℕ) (B : Box Tagged) : Meter ExportBox :=
  let h := prepareHeader a B.key
  let s := packRanks kR kC b q a h.result.2 (encodeBits q 0) B.rows
  ⟨⟨B.key,h.result.1,h.result.2,s.result⟩,h.steps+s.steps+2*b+q+12⟩

def exportBoxCap (kR kC b q a count : ℕ) : ℕ :=
  headerCap a + count*seatStepCap kR kC b q a+2*b+q+12

def validBox (a pages q : ℕ) (B : Box Tagged) : Prop :=
  ∃ c : Cell (Fin a) (Fin 64), B.key=wordCell c ∧
    B.rows.length<2^q ∧ B.rows.length≤pages*2^a ∧
    ∀ e∈B.rows, rawCell e.edge=some B.key

theorem exportBox_exact (kR kC b q a pages : ℕ) (hq : 0<q) (ha : a≤q) (B : Box Tagged)
    (hB : validBox a pages q B) :
    let x := exportBox kR kC b q a B
    x.result.key=B.key ∧ x.result.rows.map Seated.tag=B.rows ∧
    (∃ c : Cell (Fin a) (Fin 64), B.key=wordCell c ∧
      x.result.axes=axesOf c ∧ x.result.flags=marksOf c ∧
      ∀ i : Fin B.rows.length, ∃ t,
        x.result.rows[i.val]?=some t ∧ t.tag=B.rows[i] ∧
        rawCell t.tag.edge=some B.key ∧
        t.address=(seatWords (marksOf c) (encodeBits q i.val)).result ∧
        ∃ hp : bitsValue t.address.page<pages,
          physicalCell (fun _ _ _ => false) (decodePhysical c t.address hp)=c) ∧
    x.steps≤exportBoxCap kR kC b q a B.rows.length := by
  obtain ⟨c,hk,hfit,hl,hm⟩ := hB
  let h := prepareHeader a B.key
  have H : h.result=(axesOf c,marksOf c) ∧ h.steps≤headerCap a := by
    change (prepareHeader a B.key).result=_ ∧ (prepareHeader a B.key).steps≤_
    rw [hk]
    exact prepareHeader_exact c
  have hl' : h.result.1=axesOf c := congrArg Prod.fst H.1
  have hr' : h.result.2=marksOf c := congrArg Prod.snd H.1
  let s := packRanks kR kC b q a h.result.2 (encodeBits q 0) B.rows
  obtain ⟨hs,hcost⟩ := packRanks_exact kR kC b q a hq h.result.2
    (by rw [hr',marksOf_len]) ha 0 B.rows (by simpa using hfit)
  change s.result=_ at hs
  change s.steps≤_ at hcost
  rw [hr'] at hs
  refine ⟨rfl,?_,⟨c,hk,hl',hr',?_⟩,?_⟩
  · change s.result.map Seated.tag=_
    rw [hs,ranksSpec_tags]
  · intro i
    let T := (seatWords (marksOf c) (encodeBits q i.val)).result
    let U : Seated := ⟨B.rows[i],T⟩
    have hi : i.val<B.rows.length := i.isLt
    have hlen : a≤(encodeBits q i.val).length := by rwa [encodeBits_length]
    have hR : bitsValue (encodeBits q i.val)<pages*2^a := by
      rw [encodeBits_exact _ _ (hi.trans hfit)]
      exact hi.trans_le hl
    have hp : bitsValue T.page<pages :=
      page_in_range (marksOf c) (encodeBits q i.val) (by rwa [marksOf_len]) pages (by rwa [marksOf_len])
    refine ⟨U,?_,rfl,hm _ (List.getElem_mem hi),rfl,⟨hp,?_⟩⟩
    · change s.result[i.val]?=some U
      rw [hs,ranksSpec_at]
      simp [U,T,hi]
    · exact (realPhysical_single c (encodeBits q i.val) hlen hR).1
  · change h.steps+s.steps+2*b+q+12≤_
    unfold exportBoxCap
    omega

#print axioms exportBox_exact
end J6R14LayoutCost

