import J6R32ChildResidentTransferMask
import J6R31RootResidentTablesSeat

/-! Convert one paid descendant rank/address to the R27 seat ABI. The
raw ordered cell supplies the group labels; the decoded *page* selector
instead supplies the installed bit flips. The two cannot be interchanged. -/
namespace J6R32ChildResidentTransfer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open P11FullPacking J6R15ModeCost J6R17ModeTape J6R27OriginalGate
open J6R30GeneratedRootLayout J6R14LayoutCost J6R12CollisionEdges J6R24LegalLayout J6R31RootResidentTables J6R23PaddingCensus
set_option maxHeartbeats 14000000
set_option maxRecDepth 2200

def childPageKey {a b : ℕ} (w : ℕ) (page : Page a b (Fin 64)) : Word (w+13*a) :=
  ⟨(pageWord w page).val,(pageWord w page).property⟩

theorem child_page_key_injective {a b : ℕ} (w : ℕ) (fit : b≤2^w) :
    Function.Injective (childPageKey (a:=a) (b:=b) w) := by
  intro p q eq
  exact (page_code_injective w fit).eq_iff.mp
    (congrArg (fun k : Word (w+13*a)=>bitsValue k.bits) eq)

def selectorFlagTape (xs : List AxisWord) (s : List Bool) : Meter (List Bool) :=
  mapMeter (fun p : AxisWord×Bool=>⟨p.1.unequal && p.2,2⟩) (xs.zip s)

theorem selector_flags_exact {a b : ℕ} (c : CellType a) (s : SeatWords)
    (len : s.selector.length=a) (hp : bitsValue s.page<b) :
    let F := selectorFlagTape (axesOf c) s.selector
    F.result=List.ofFn (maskWordAt (childMask a b) (decodePhysical c s hp).1) ∧ F.steps≤8*a := by
  let f := fun i : Fin a=>s.selector.getD i.val false
  have H : s.selector=List.ofFn f := list_from_values false s.selector len f (fun _=>rfl)
  obtain ⟨sh,sf⟩ := mapMeter_exact (fun p : AxisWord×Bool=>⟨p.1.unequal && p.2,2⟩)
    (fun p=>p.1.unequal && p.2) 2 ((axesOf c).zip s.selector) (fun _ _=>⟨rfl,le_rfl⟩)
  change (selectorFlagTape (axesOf c) s.selector).result=_ at sh
  change (selectorFlagTape (axesOf c) s.selector).steps≤_ at sf
  have hL : ((axesOf c).zip s.selector).length=a := by
    rw [H,axesOf,zip_fn,List.length_ofFn]
  rw [hL] at sf
  refine ⟨sh.trans ?_,sf⟩
  rw [H,axesOf,zip_fn,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (decide ((c i).1≠(c i).2) && f i) =
    (if h : (sortPair (c i)).1≠(sortPair (c i)).2 then f i else false)
  by_cases h : (c i).1≠(c i).2
  · rw [dif_pos ((sorted_hot _ _).mp h),decide_eq_true h]
    rfl
  · rw [dif_neg (fun G=>h ((sorted_hot _ _).mpr G)),decide_eq_false h]
    rfl

def writeMaskedSeat (a w : ℕ) (axis : List Bool) (x : AnchorWord) :
    Meter (SeatField a (w+13*a)) :=
  let s := buildSeatField a w axis x
  let F := selectorFlagTape x.physical.axes x.physical.seat.selector
  let q := flipTape s.result.slot.bits F.result
  let slot := fitWord a q.result
  ⟨{s.result with slot:=slot.result},s.steps+F.steps+q.steps+slot.steps+8⟩

def maskedSeatFee (a w : ℕ) := seatStride a w+22*a+14

theorem raw_masked_seat_exact {a b w : ℕ} (i : Fin a) (axis : List Bool)
    (clock : axis.length=i.val) (c : CellType a) (x : AnchorWord)
    (hCell : x.cell=wordCell c) (hAxes : x.physical.axes=axesOf c)
    (hSlot : x.physical.seat.slot.length=a)
    (hMask : x.physical.seat.selector.length=a) (hPage : x.physical.seat.page.length=w)
    (fits : bitsValue x.physical.seat.page<b) :
    let u := decodePhysical c x.physical.seat fits
    let z := twistSeat (childMask a b) u
    let op := writeMaskedSeat a w axis x
    op.result=⟨childPageKey w z.1,word z.2.val,word ((c i).1.val),word ((c i).2.val)⟩ ∧
      op.steps≤maskedSeatFee a w := by
  let s := x.physical.seat
  let u := decodePhysical c s fits
  let z := twistSeat (childMask a b) u
  let B := buildSeatField a w axis x
  have F := emit_axis_tape_exact x.physical.axes s.selector (fun y hy=>by
    rw [hAxes,axesOf,List.mem_ofFn] at hy
    obtain ⟨j,rfl⟩ := hy
    exact ⟨symbol_length _,symbol_length _⟩)
  let A := emitAxisTape x.physical.axes s.selector
  let J := appendBits s.page A.result
  have Jv : J.result=(childPageKey w u.1).bits := by
    change (appendBits s.page (emitAxisTape x.physical.axes s.selector).result).result=_
    rw [append_bits_exact,F.1,hAxes]
    exact decode_page_fields c s hMask hPage fits
  have p : B.result.page=childPageKey w z.1 := by
    apply word_bits_inj
    change (fitWord (w+13*a) J.result).result.bits=(childPageKey w u.1).bits
    have l : J.result.length=w+13*a := Jv ▸ (childPageKey w u.1).size
    rw [fit_word_value _ _ l,Jv]
  have K : B.result.slot.bits=s.slot := by
    change (fitWord a s.slot).result.bits=s.slot
    exact fit_word_value _ _ hSlot
  have Q1 : (readSymbol axis x.cell.1).result=symbol ((c i).1) := by
    rw [hCell]
    exact coordinate_word_at i axis clock (fun j=>(c j).1)
  have Q2 : (readSymbol axis x.cell.2).result=symbol ((c i).2) := by
    rw [hCell]
    exact coordinate_word_at i axis clock (fun j=>(c j).2)
  have R : B.result.rowGroup=word ((c i).1.val) := by
    apply word_bits_inj
    change (fitWord 6 (readSymbol axis x.cell.1).result).result.bits=_
    rw [Q1,fit_word_value _ _ (symbol_length _)]
    rfl
  have C : B.result.colGroup=word ((c i).2.val) := by
    apply word_bits_inj
    change (fitWord 6 (readSymbol axis x.cell.2).result).result.bits=_
    rw [Q2,fit_word_value _ _ (symbol_length _)]
    rfl
  let fs := selectorFlagTape x.physical.axes s.selector
  have hx : fs.result=List.ofFn (maskWordAt (childMask a b) u.1) ∧ fs.steps≤8*a := by
    change (selectorFlagTape x.physical.axes s.selector).result=_ ∧ (selectorFlagTape x.physical.axes s.selector).steps≤_
    rw [hAxes]
    exact selector_flags_exact c s hMask fits
  have Zb : s.slot=List.ofFn (bits a u.2) := by
    apply list_from_values false _ hSlot
    intro j
    change s.slot.getD j.val false=bits a ((bitsChart a).symm (fun k=>s.slot.getD k.val false)) j
    have h := congrFun ((bitsChart a).apply_symm_apply (fun k : Fin a=>s.slot.getD k.val false)) j
    change bits a ((bitsChart a).symm (fun k=>s.slot.getD k.val false)) j=s.slot.getD j.val false at h
    exact h.symm
  let D := flipTape B.result.slot.bits fs.result
  have Dv : D.result=List.ofFn (bits a z.2) ∧ D.steps=4+8*a := by
    change (flipTape B.result.slot.bits fs.result).result=_ ∧ (flipTape B.result.slot.bits fs.result).steps=_
    rw [K,Zb,hx.1]
    exact actual_slot_flip_word (childMask a b) u
  have hWord : (fitWord a D.result).result=word z.2.val := by
    apply word_bits_inj
    rw [Dv.1,fit_word_value _ _ List.length_ofFn]
    symm
    exact list_from_values false (encodeBits a z.2.val) (encodeBits_length _ _) _
      (fun j=>encoded_bit_at a z.2.val j.val j.isLt)
  constructor
  · change SeatField.mk B.result.page (fitWord a D.result).result B.result.rowGroup B.result.colGroup=_
    rw [p,hWord,R,C]
  · have hA : A.steps≤3+60*a := by
      exact F.2.trans_eq (by rw [hAxes,axesOf,List.length_ofFn])
    have hJ : J.steps=2+4*w := by
      unfold J
      rw [append_bits_exact]
      exact congrArg (fun k=>2+4*k) hPage
    have ar : axis.length≤a := clock ▸ i.isLt.le
    have br := read_symbol_fee axis x.cell.1
    have bc := read_symbol_fee axis x.cell.2
    have hB : B.steps≤seatStride a w := by
      change A.steps+J.steps+(fitWord (w+13*a) J.result).steps+(fitWord a s.slot).steps+
        (readSymbol axis x.cell.1).steps+(readSymbol axis x.cell.2).steps+
        (fitWord 6 (readSymbol axis x.cell.1).result).steps+
        (fitWord 6 (readSymbol axis x.cell.2).result).steps+12≤_
      rw [hJ]
      simp only [fit_word_fee]
      unfold seatStride
      omega
    change B.steps+fs.steps+D.steps+(fitWord a D.result).steps+8≤_
    rw [Dv.2,fit_word_fee]
    unfold maskedSeatFee
    omega

#print axioms child_page_key_injective
#print axioms selector_flags_exact
#print axioms raw_masked_seat_exact
end J6R32ChildResidentTransfer