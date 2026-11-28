
import J6R27OriginalGateModeCompare
import J6R21AncestorGather

/-! Read the actual selected coordinate of a packed symbol word, and read
the high tile bit from a raw mode record. The same ordered page cell can
have either orientation at the tile: ownership must also use the actual
page mask, not just its unshifted ordering. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R14LayoutCost J6R21Ancestor
open P11FullPacking J6R9PacketScopes

def readSymbol : List Bool→List Bool→Meter (List Bool)
  | [],bs =>
    let z := copyBytes (bs.take 6)
    ⟨z.result,z.steps+16⟩
  | _::ticks,bs =>
    let z := readSymbol ticks (bs.drop 6)
    ⟨z.result,z.steps+16⟩

theorem read_symbol_fee (ticks bs : List Bool) : (readSymbol ticks bs).steps≤16*ticks.length+35 := by
  induction ticks generalizing bs with
  | nil =>
    simp only [readSymbol,copyBytes_exact,List.length_nil,Nat.mul_zero,Nat.zero_add]
    have H := List.length_take_le 6 bs
    omega
  | cons t tt ih =>
    have H := ih (bs.drop 6)
    simp only [readSymbol,List.length_cons,Nat.mul_succ]
    omega

theorem read_symbol_is_index (ticks : List Bool) (xs : List (Fin 64))
    (valid : ticks.length<xs.length) :
    (readSymbol ticks (symbolTape xs)).result=symbol xs[ticks.length] := by
  induction ticks generalizing xs with
  | nil =>
    cases xs with
    | nil => exact (Nat.lt_irrefl _ valid).elim
    | cons x xs =>
      change (copyBytes ((symbol x++symbolTape xs).take 6)).result=symbol x
      rw [symbol_take_append,copyBytes_exact]
  | cons t rest ih =>
    cases xs with
    | nil => simp at valid
    | cons x xs =>
      have hlt : rest.length<xs.length := Nat.lt_of_succ_lt_succ valid
      change (readSymbol rest ((symbol x++symbolTape xs).drop 6)).result=symbol (getElem xs rest.length hlt)
      rw [symbol_drop_append]
      exact ih xs hlt

theorem coordinate_word_at {a : ℕ} (i : Fin a) (ticks : List Bool) (len : ticks.length=i.val)
    (x : Fin a→Fin 64) :
    (readSymbol ticks (coordinateLabel x)).result=symbol (x i) := by
  have h : ticks.length<(List.ofFn x).length := by rw [List.length_ofFn,len]; exact i.isLt
  rw [coordinateLabel,read_symbol_is_index ticks _ h,List.getElem_ofFn]
  congr 2
  exact Fin.ext len

theorem encoded_bit_at (q x j : ℕ) (fit : j<q) :
    (encodeBits q x).getD j false=x.testBit j := by
  induction j generalizing q x with
  | zero =>
    cases q with
    | zero => exact (Nat.lt_irrefl _ fit).elim
    | succ q => simp [encodeBits]
  | succ j ih =>
    cases q with
    | zero => simp at fit
    | succ q =>
      change (encodeBits q (x/2)).getD j false=x.testBit (j+1)
      rw [Nat.testBit_succ]
      exact ih q (x/2) (Nat.lt_of_succ_lt_succ fit)

def runtimeGroupPair {q : ℕ} (axis : List Bool) (key : CellWord) (tile : Word q)
    (pageMaskBit : Bool) : Meter (List Bool×List Bool) :=
  let l := readSymbol axis key.1
  let r := readSymbol axis key.2
  let s := sortAxis l.result r.result
  let b := readSkip axis tile.bits
  let flip := if b.result then !pageMaskBit else pageMaskBit
  ⟨if flip then (s.result.high,s.result.low) else (s.result.low,s.result.high),
    l.steps+r.steps+s.steps+b.steps+14⟩

def selectedMaskBit {a b : ℕ} (mask : MaskFamily a b (Fin 64))
    (page : Page a b (Fin 64)) (i : Fin a) : Bool :=
  if h : (page.1.val i).1≠(page.1.val i).2 then mask page.1 page.2 ⟨i,h⟩ else false

set_option maxHeartbeats 2400000 in
theorem group_pair_is_physical {a b q : ℕ} (i : Fin a) (ticks : List Bool) (len : ticks.length=i.val)
    (width : i.val<q) (mask : MaskFamily a b (Fin 64)) (page : Page a b (Fin 64))
    (tile : Fin (2^(i.val+1))) :
    let key := wordCell (cell page.1 page.2.2)
    let t := word (q:=q) tile.val
    let M := runtimeGroupPair ticks key t (selectedMaskBit mask page i)
    M.result=(symbol (rowGroup mask i (page,tileIndex i tile)),
      symbol (colGroup mask i (page,tileIndex i tile))) ∧ M.steps≤36*i.val+238 := by
  let c := cell page.1 page.2.2
  let k := wordCell c
  let t := word (q:=q) tile.val
  let l := readSymbol ticks k.1
  let r := readSymbol ticks k.2
  let s := sortAxis l.result r.result
  let tB := readSkip ticks t.bits
  have lE : l.result=symbol (c i).1 := coordinate_word_at i ticks len (fun j=>(c j).1)
  have rE : r.result=symbol (c i).2 := coordinate_word_at i ticks len (fun j=>(c j).2)
  have LL := read_symbol_fee ticks k.1
  have RR := read_symbol_fee ticks k.2
  have hS : s.result=axisSpec (c i).1 (c i).2 ∧ s.steps=152 := by
    change (sortAxis l.result r.result).result=_ ∧ (sortAxis l.result r.result).steps=_
    rw [lE,rE]
    exact sortAxis_exact _ _
  have bk : tB.result=tile.val.testBit i.val ∧ tB.steps≤4*ticks.length+2 := by
    obtain ⟨h,v⟩ := readSkip_exact ticks t.bits
    refine ⟨?_,v⟩
    change tB.result=_ at h
    rw [h,len]
    exact encoded_bit_at q tile.val i.val width
  have sorted : sortPair (c i)=page.1.val i :=
    congrFun (congrArg Subtype.val (key_cell page.1 page.2.2)) i
  dsimp only
  constructor
  · change (if (if tB.result then !selectedMaskBit mask page i else selectedMaskBit mask page i)
        then (s.result.high,s.result.low) else (s.result.low,s.result.high))=_
    rw [hS.1,bk.1]
    simp only [axisSpec,sorted]
    change _=(symbol ((physicalCell mask (page,tileIndex i tile)) i).1,
      symbol ((physicalCell mask (page,tileIndex i tile)) i).2)
    unfold physicalCell cell
    by_cases h : (page.1.val i).1≠(page.1.val i).2
    · simp only [dif_pos h,selectedMaskBit,slotOrient,shiftMask,bits,tileIndex,Fin.coe_castLE]
      cases hR : mask page.1 page.2 ⟨i,h⟩ <;>
        cases bit : tile.val.testBit i.val <;> simp
    · simp only [dif_neg h,selectedMaskBit]
      have hSym := not_ne_iff.mp h
      rw [hSym]
      split <;> rfl
  · change l.steps+r.steps+s.steps+tB.steps+14≤_
    rw [hS.2]
    change l.steps≤16*ticks.length+35 at LL
    change r.steps≤16*ticks.length+35 at RR
    have hh := bk.2
    omega

#print axioms read_symbol_is_index
#print axioms coordinate_word_at
#print axioms encoded_bit_at
#print axioms group_pair_is_physical
end J6R27OriginalGate





