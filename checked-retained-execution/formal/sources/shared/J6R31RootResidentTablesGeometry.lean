
import J6R30GeneratedRootLayoutReceipt
import J6R27OriginalGateSlots
import J6R27OriginalGateAxis
import J6R23PaddingCensusCodec

/-! Decode exactly the page/slot needed by the R27 seat ABI from the
paid R30 anchor. The page keeps its selector, even when the currently
occupied ordered cell has the opposite orientation. -/
namespace J6R31RootResidentTables
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R30GeneratedRootLayout J6R24LegalLayout J6R14LayoutCost J6R23PaddingCensus
open J6Mesh P11FullPacking J6R15ModeCost J6R27OriginalGate J6R21Ancestor
set_option maxHeartbeats 13000000
set_option maxRecDepth 2000

theorem words_shape (m : ℕ) (e : RootWire m) :
    let x := (sourceAnchor m e).anchor
    x.physical.axes=axesOf (rankAt m e).1 ∧
      x.physical.seat.page.length=RootKey m ∧
      x.physical.seat.slot.length=a m ∧ x.physical.seat.selector.length=a m := by
  let c := (rankAt m e).1
  let r := encodeBits (printedRankWidth m) (rankAt m e).2.val
  have edge : (sourceAnchor m e).anchor.physical=(exportOne (a m) (wordCell c) r).result := rfl
  have H := (prepareHeader_exact c).1
  have W := seatWords_exact (marksOf c) r (by
    rw [marksOf_len,encodeBits_length]
    exact (printed_rank_width m).2.1)
  have S : (exportOne (a m) (wordCell c) r).result.seat=(seatWords (marksOf c) r).result := by
    change (seatWords (prepareHeader (a m) (wordCell c)).result.2 r).result=_
    rw [H]
  have X : (exportOne (a m) (wordCell c) r).result.axes=axesOf c := by
    change (prepareHeader (a m) (wordCell c)).result.1=_
    rw [H]
  change (sourceAnchor m e).anchor.physical.axes=axesOf c ∧ _
  rw [edge,X,S,W.2.2.2.2.1,List.length_drop,encodeBits_length,marksOf_len,W.1,W.2.1]
  simp only [RootKey,marksOf_len,and_self]

theorem list_from_values {B : Type*} {n : ℕ} (d : B) (xs : List B) (len : xs.length=n)
    (f : Fin n→B) (E : ∀ i,xs.getD i.val d=f i) : xs=List.ofFn f := by
  apply List.ext_getElem (by rw [List.length_ofFn,len])
  intro i hi hj
  have P : i<n := hi.trans_eq len
  have eq := E ⟨i,P⟩
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] at eq
  rw [List.getElem_ofFn]
  exact eq

theorem zip_fn {A B : Type*} {n : ℕ} (f : Fin n→A) (g : Fin n→B) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun j=>(f j,g j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ,List.zip_cons_cons,ih]

theorem fixed_concat_as_flat {n : ℕ} (xs : List (A1R10.Word n)) :
    fixedConcat xs=xs.flatMap Subtype.val := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [fixedConcat,List.flatMap_cons,ih]

def axisBytes (x : AxisWord) (bit : Bool) : List Bool :=
  x.low++(x.high++[x.unequal && bit])

def axisPayload (xs : List AxisWord) (bs : List Bool) : List Bool :=
  (xs.zip bs).flatMap (fun x=>axisBytes x.1 x.2)

theorem sorted_hot (x y : Fin 64) :
    (x≠y) ↔ (sortPair (x,y)).1≠(sortPair (x,y)).2 := by
  unfold sortPair
  split <;> simp [ne_comm]

theorem axis_payload_actual {a b : ℕ} (c : CellType a) (s : SeatWords)
    (len : s.selector.length=a) (hp : bitsValue s.page<b) :
    axisPayload (axesOf c) s.selector =
      fixedConcat (List.ofFn (axisRecord (decodePhysical c s hp).1)) := by
  let f := fun i : Fin a=>s.selector.getD i.val false
  have sel := list_from_values false s.selector len f (fun _=>rfl)
  have EACH (i : Fin a) :
      axisBytes (axisSpec (c i).1 (c i).2) (f i) =
        (axisRecord (decodePhysical c s hp).1 i).val := by
    change symbol (sortPair (c i)).1++(symbol (sortPair (c i)).2++
       [decide ((c i).1≠(c i).2) && f i])=
      encodeBits 6 (sortPair (c i)).1.val++(encodeBits 6 (sortPair (c i)).2.val++
       [axisSelector (decodePhysical c s hp).1 i])
    have eqBit : (decide ((c i).1≠(c i).2) && f i)=
        axisSelector (decodePhysical c s hp).1 i := by
      unfold axisSelector
      change (decide ((c i).1≠(c i).2) && f i)=
        (if h : (sortPair (c i)).1≠(sortPair (c i)).2 then f i else false)
      by_cases h : (c i).1≠(c i).2
      · rw [dif_pos ((sorted_hot _ _).mp h),decide_eq_true h]
        rfl
      · rw [dif_neg (fun G=>h ((sorted_hot _ _).mpr G)),decide_eq_false h]
        rfl
    rw [eqBit]
    rfl
  rw [axisPayload,axesOf,sel,zip_fn,fixed_concat_as_flat]
  change ((List.ofFn (fun i : Fin a=>(axisSpec (c i).1 (c i).2,f i))).map
      (fun z=>axisBytes z.1 z.2)).flatten=
        ((List.ofFn (axisRecord (decodePhysical c s hp).1)).map Subtype.val).flatten
  congr 1
  rw [List.map_ofFn,List.map_ofFn]
  exact congrArg List.ofFn (funext EACH)

theorem decode_slot_literal {a b : ℕ} (c : CellType a) (s : SeatWords)
    (len : s.slot.length=a) (hb : bitsValue s.page<b) :
    s.slot=encodeBits a (decodePhysical c s hb).2.val := by
  let z := (decodePhysical c s hb).2
  have B := (bitsChart a).apply_symm_apply (fun j=>s.slot.getD j.val false)
  have A (i : Fin a) : s.slot.getD i.val false=z.val.testBit i.val := by
    have h : bits a z i=s.slot.getD i.val false := congrFun B i
    exact h.symm
  have ex := list_from_values false s.slot len (fun j=>z.val.testBit j.val) A
  have ey := list_from_values false (encodeBits a z.val) (encodeBits_length _ _)
      (fun j=>z.val.testBit j.val) (fun j=>encoded_bit_at a z.val j.val j.isLt)
  exact ex.trans ey.symm

theorem decode_page_fields {a b w : ℕ} (c : CellType a) (s : SeatWords)
    (sel : s.selector.length=a) (sz : s.page.length=w) (hp : bitsValue s.page<b) :
    s.page++axisPayload (axesOf c) s.selector =
      (pageWord w (decodePhysical c s hp).1).val := by
  have fits : bitsValue s.page<2^w := by simpa only [sz] using bitsValue_lt s.page
  have enc : encodeBits w (bitsValue s.page)=s.page := by
    apply J6R29BinaryFieldSearch.equal_width_inj
    · rw [encodeBits_length,sz]
    · exact encodeBits_exact _ _ fits
  change s.page++axisPayload (axesOf c) s.selector =
    encodeBits w (bitsValue s.page)++fixedConcat (List.ofFn (axisRecord (decodePhysical c s hp).1))
  rw [axis_payload_actual c s sel hp,enc]

#print axioms words_shape
#print axioms axis_payload_actual
#print axioms decode_slot_literal
#print axioms decode_page_fields
end J6R31RootResidentTables
