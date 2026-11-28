import J6R75RawPeakStockRegisters

/-! A real restoring divide digit in the stock's shared height word.
The named fields include the reversed input, actual pending quotient and
remainder, padded subtract operands, resolved borrow and successor.
This is not the whole recursive borrow implementation's heap. -/
namespace J6R75RawPeak
open AOracleMachineTime A1R10 J6R68ActiveInputs J6R22RootReadout J6R52FreshExterior
open AAcquisitionCost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3600
set_option maxHeartbeats 5700000
set_option Elab.async false

theorem divide_digits_reenter_their_actual_prefix
    (divisor pre post : List Bool) (state : List Bool×List Bool) :
    divisionDigits divisor (pre++post) state=
      divisionDigits divisor post (divisionDigits divisor pre state) := by
  induction pre generalizing state with
  | nil=>rfl
  | cons b bs ih=>
    exact ih (let prior := divideDigit divisor state.2 b
      (prior.1::state.1,prior.2))

private theorem digit_remainder_keeps_divisor_width
    (divisor remainder : List Bool) (b : Bool) (width : remainder.length=divisor.length) :
    (divideDigit divisor remainder b).2.length=divisor.length := by
  let z := b::remainder
  let pad := divisor++[false]
  let cut := rippleBorrow z pad false
  have same : z.length=pad.length := by simp [z,pad,width]
  have diff : cut.1.length=divisor.length+1 :=
    (rippleBorrow_length z pad false same).trans (by simp [z,width])
  change ((if cut.2 then z else cut.1).take divisor.length).length=divisor.length
  split
  · simp [z,width]
  · simp [diff]

theorem divide_digits_preserve_the_real_remainder_width
    (divisor digits : List Bool) (state : List Bool×List Bool)
    (width : state.2.length=divisor.length) :
    (divisionDigits divisor digits state).2.length=divisor.length := by
  induction digits generalizing state with
  | nil=>exact width
  | cons b bs ih=>
    let nxt := divideDigit divisor state.2 b
    exact ih (nxt.1::state.1,nxt.2) (digit_remainder_keeps_divisor_width divisor state.2 b width)

def StockHeightDivisionCut {q : ℕ} (x d : Word q) (pre : List Bool) (b : Bool) (post : List Bool)
    (resident roof : ℕ) : Prop :=
  let state := divisionDigits d.val pre ([],List.replicate q false)
  let shifted := b::state.2
  let padded := d.val++[false]
  let sub := rippleBorrow shifted padded false
  let next := divideDigit d.val state.2 b
  let successor := (next.1::state.1,next.2)
  x.val.reverse=pre++b::post ∧
  (divideMagnitude x d).result.val=(divisionDigits d.val post successor).1 ∧
  resident+(x.val.length+x.val.reverse.length+d.val.length+state.1.length+state.2.length+
    shifted.length+padded.length+sub.1.length+successor.1.length+successor.2.length+2)≤roof+(10*q+5)

theorem actual_restoring_divide_digit_has_named_work_space
    {q : ℕ} (x d : Word q) (pre : List Bool) (b : Bool) (post : List Bool)
    (cut : x.val.reverse=pre++b::post)
    (resident roof : ℕ) (fit : resident≤roof) :
    StockHeightDivisionCut x d pre b post resident roof := by
  let init := (([] : List Bool),List.replicate q false)
  let state := divisionDigits d.val pre init
  let shifted := b::state.2
  let padded := d.val++[false]
  let sub := rippleBorrow shifted padded false
  let next := divideDigit d.val state.2 b
  let successor := (next.1::state.1,next.2)
  have xs : x.val.reverse.length=q := by rw [List.length_reverse,x.property]
  have plen : pre.length+1≤q := by
    rw [cut,List.length_append,List.length_cons] at xs
    omega
  have quo : state.1.length=pre.length := by
    change (divisionDigits d.val pre init).1.length=_
    rw [quotient_trace_length]
    simp [init]
  have remLen : state.2.length=q :=
    (divide_digits_preserve_the_real_remainder_width _ _ _ (by simp [init,d.property])).trans d.property
  have enlarged : shifted.length=q+1 := by simp [shifted,remLen]
  have padLen : padded.length=q+1 := by simp [padded,d.property]
  have subLen : sub.1.length=q+1 :=
    (rippleBorrow_length shifted padded false (enlarged.trans padLen.symm)).trans enlarged
  have newQ : successor.1.length=pre.length+1 := by simp [successor,quo]
  have newR : successor.2.length=q :=
    (digit_remainder_keeps_divisor_width d.val state.2 b (remLen.trans d.property.symm)).trans d.property
  refine ⟨cut,?_,?_⟩
  · change (binaryDivide d.val x.val.reverse)=(divisionDigits d.val post successor).1
    rw [cut,binaryDivide,divide_digits_reenter_their_actual_prefix,d.property]
    rfl
  · change resident+(x.val.length+x.val.reverse.length+d.val.length+state.1.length+state.2.length+
      shifted.length+padded.length+sub.1.length+successor.1.length+successor.2.length+2)≤_
    rw [x.property,xs,d.property,quo,remLen,enlarged,padLen,subLen,newQ,newR]
    exact Nat.add_le_add fit (by omega)

def literalStockHeightNumerator {q : ℕ} (hq : 0<q) (edge taper : J6R15ModeCost.Word q) :
    Word q :=
  let E := modeWordAsA edge
  let U := modeWordAsA taper
  let o := (constantRegister q [true]).result
  let t := (constantRegister q [true,true]).result
  let extra := (subWord hq U o).result
  let triple := (mulWord t E).result
  (addWord triple extra).result

theorem raw_stock_height_has_an_actual_named_restoring_cut
    {q : ℕ} (hq : 0<q) (edge taper : J6R15ModeCost.Word q)
    (pre : List Bool) (b : Bool) (post : List Bool)
    (hit : (literalStockHeightNumerator hq edge taper).val.reverse=pre++b::post)
    (resident roof : ℕ) (fit : resident≤roof) :
    let num := literalStockHeightNumerator hq edge taper
    let den := modeWordAsA taper
    (heightWord hq edge taper).result=(divideMagnitude num den).result ∧
    StockHeightDivisionCut num den pre b post resident roof :=
  ⟨rfl,actual_restoring_divide_digit_has_named_work_space _ _ pre b post hit resident roof fit⟩

#print axioms divide_digits_reenter_their_actual_prefix
#print axioms divide_digits_preserve_the_real_remainder_width
#print axioms actual_restoring_divide_digit_has_named_work_space
#print axioms raw_stock_height_has_an_actual_named_restoring_cut
end J6R75RawPeak
