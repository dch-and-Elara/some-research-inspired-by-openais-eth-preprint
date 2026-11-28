import J6R33PageIndexedBirthBank
import J6R32ChildResidentTransferSeat

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4600000

/-! A page request is computed from its ordered-cell header and copy
number, not from an occupied slot's orientation or a postulated key.
The same encoding is used by root and descendant seat files. -/
namespace J6R33PageIndexedBirth
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R15ModeCost J6R27OriginalGate J6R14LayoutCost J6R31RootResidentTables
open J6R32ChildResidentTransfer J6R23PaddingCensus P11FullPacking OuterNodePacking
open J6R12CollisionEdges J6R24LegalLayout J6R17ModeTape J6R30GeneratedRootLayout

theorem fit_getD (n : ℕ) (xs : List Bool) (j : ℕ) (inWidth : j<n) :
    (fitBits n xs).result.getD j false=xs.getD j false := by
  induction n generalizing xs j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => cases xs <;> rfl
    | succ j =>
      cases xs with
      | nil =>
        have z := ih [] j (by omega)
        simpa only [fitBits,List.tail_nil,List.getD_cons_succ,List.getD_nil] using z
      | cons x xs =>
        simpa only [fitBits,List.tail_cons,List.getD_cons_succ] using ih xs j (by omega)

theorem resize_low_word (w q n : ℕ) (hq : n<2^q) :
    (fitWord w (word (q:=q) n).bits).result=word (q:=w) n := by
  apply word_bits_inj
  let raw := (word (q:=q) n).bits
  let Y := fitWord w raw
  have h (j : Fin w) : Y.result.bits.getD j.val false=n.testBit j.val := by
    change (fitBits w raw).result.getD j.val false=_
    rw [fit_getD w raw j.val j.isLt]
    change (encodeBits q n).getD j.val false=_
    by_cases jQ : j.val<q
    · exact encoded_bit_at q n _ jQ
    · have jge : q≤j.val := Nat.le_of_not_gt jQ
      have hj := hq.trans_le (Nat.pow_le_pow_right (by decide) jge)
      have hb : n.testBit j.val=false := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hj]
        rfl
      rw [hb]
      have off : (encodeBits q n).length≤j.val := by rwa [encodeBits_length]
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none off]
  change Y.result.bits=_
  rw [list_from_values false Y.result.bits Y.result.size _ h]
  symm
  exact list_from_values false (encodeBits w n) (encodeBits_length _ _) _
    (fun j=>encoded_bit_at w n _ j.isLt)

noncomputable def sourceRequest {a b : ℕ} (q w : ℕ) (page : Page a b (Fin 64)) :
    Request q (w+13*a) :=
  ⟨pageRef q page,childPageKey w page⟩

def selectorBits (B : ExportBox) : Meter (List Bool) :=
  mapMeter (fun x : Bool×Bool => ⟨x.2,2⟩) B.flags

def emitRequest {q : ℕ} (a w : ℕ) (B : ExportBox) (id : Word q) :
    Meter (Request q (w+13*a)) :=
  let mark := selectorBits B
  let sel := emitAxisTape B.axes mark.result
  let cp := fitWord w id.bits
  let bytes := appendBits cp.result.bits sel.result
  let out := fitWord (w+13*a) bytes.result
  let lo := appendBits B.key.1 []
  let hi := appendBits B.key.2 []
  let num := copyFixed id
  ⟨⟨⟨(lo.result,hi.result),num.result⟩,out.result⟩,
    mark.steps+sel.steps+cp.steps+bytes.steps+out.steps+lo.steps+hi.steps+num.steps+15⟩

def requestFee (a w q : ℕ) := 300*a+30*w+10*q+100

theorem order_page_at {a b : ℕ} (c : CellType a) (j : Fin b) :
    (orderedPage a b).symm (c,j)=⟨key c,(j,orientation c)⟩ := by
  apply (orderedPage a b).injective
  rw [Equiv.apply_symm_apply]
  change (c,j)=(cell (key c) (orientation c),j)
  rw [cell_decode]

theorem emitted_request_exact {a b : ℕ} (c : CellType a) (j : Fin b)
    (q w : ℕ) (fitQ : b≤2^q) (fitW : b≤2^w) :
    let O := emitRequest a w (headerBox c) (word (q:=q) j.val)
    O.result=sourceRequest q w ((orderedPage a b).symm (c,j)) ∧
      O.steps≤requestFee a w q := by
  let mark := selectorBits (headerBox c)
  obtain ⟨markVal,markCost⟩ := mapMeter_exact (fun x : Bool×Bool=>⟨x.2,2⟩) Prod.snd
    2 (marksOf c) (fun _ _=>⟨rfl,le_rfl⟩)
  change mark.result=(marksOf c).map Prod.snd at markVal
  change mark.steps≤(2+6)*(marksOf c).length at markCost
  rw [marksOf_len] at markCost
  have markSpec : mark.result=List.ofFn (fun k : Fin a=>decide ((c k).2<(c k).1)) := by
    rw [markVal,marksOf,List.map_ofFn]
    rfl
  let sel := emitAxisTape (axesOf c) mark.result
  obtain ⟨selVal,selSteps⟩ := emit_axis_tape_exact (axesOf c) mark.result (fun x hx=>by
    rw [axesOf,List.mem_ofFn] at hx
    obtain ⟨k,rfl⟩ := hx
    exact ⟨symbol_length _,symbol_length _⟩)
  change sel.result=_ at selVal
  change sel.steps≤_ at selSteps
  rw [axesOf,List.length_ofFn] at selSteps
  let cp := fitWord w (word (q:=q) j.val).bits
  have cpVal : cp.result=word (q:=w) j.val := resize_low_word w q j.val (j.isLt.trans_le fitQ)
  have cpNat : bitsValue cp.result.bits=j.val := by
    rw [cpVal]
    exact encodeBits_exact _ _ (j.isLt.trans_le fitW)
  let s : SeatWords := {slot := [],selector:=mark.result,page:=cp.result.bits}
  have sGood : bitsValue s.page<b := cpNat.symm ▸ j.isLt
  have sLen : s.selector.length=a := by change mark.result.length=a; rw [markSpec,List.length_ofFn]
  have qPage : (decodePhysical c s sGood).1=(orderedPage a b).symm (c,j) := by
    rw [order_page_at]
    have aE : (⟨bitsValue cp.result.bits,sGood⟩ : Fin b)=j := Fin.ext cpNat
    have fE : (fun k : Hot (key c)=>mark.result.getD k.val.val false)=orientation c := by
      funext k
      rw [markSpec,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
      simp [k.val.isLt,orientation]
    change (⟨key c,(⟨bitsValue cp.result.bits,sGood⟩,fun k=>mark.result.getD k.val.val false)⟩ :
      Page a b (Fin 64))=_
    rw [aE,fE]
  let pack := appendBits cp.result.bits sel.result
  have geom : pack.result=(childPageKey w ((orderedPage a b).symm (c,j))).bits := by
    dsimp only [pack]
    rw [append_bits_exact,selVal]
    have e := decode_page_fields c s sLen cp.result.size sGood
    change cp.result.bits++axisPayload (axesOf c) mark.result=(childPageKey w (decodePhysical c s sGood).1).bits at e
    rwa [qPage] at e
  have packSize : pack.result.length=w+13*a := geom ▸ (childPageKey w ((orderedPage a b).symm (c,j))).size
  have outVal : (fitWord (w+13*a) pack.result).result=childPageKey w ((orderedPage a b).symm (c,j)) := by
    apply word_bits_inj
    rw [fit_word_value _ _ packSize,geom]
  have k₁ : (wordCell c).1.length=6*a := coordinateLabel_len _
  have k₂ : (wordCell c).2.length=6*a := coordinateLabel_len _
  constructor
  · change Request.mk _ (fitWord (w+13*a) pack.result).result=_
    rw [outVal]
    unfold sourceRequest pageRef
    rw [Equiv.apply_symm_apply]
    simp only [append_bits_exact,List.append_nil,copy_fixed_exact]
    rfl
  · change mark.steps+sel.steps+cp.steps+pack.steps+(fitWord (w+13*a) pack.result).steps+
      (appendBits (wordCell c).1 []).steps+(appendBits (wordCell c).2 []).steps+
      (copyFixed (word (q:=q) j.val)).steps+15≤_
    unfold pack cp requestFee
    simp only [append_bits_exact,fit_word_fee,copy_fixed_exact,k₁,k₂]
    have z := (fitWord w (word (q:=q) j.val).bits).result.size
    omega

#print axioms fit_getD
#print axioms resize_low_word
#print axioms order_page_at
#print axioms emitted_request_exact
end J6R33PageIndexedBirth