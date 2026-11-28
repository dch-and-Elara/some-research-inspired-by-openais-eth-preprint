import J6R52FreshExteriorWordsMenu
import J6R19RetainedWords

/-! Construct the physical initial words, using a single retained
precision tape, not three prevalidated output words. The copy count
is the printed one-hot constant, emitted directly by a bit loop.
All destination widths have explicit no-truncation guards. -/
namespace J6R52FreshExterior
open scoped Classical
open J6Mesh J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R15ModeCost J6R19Retained J6R24LegalLayout
open A1R12 AOracleMachineTime AOracleMachineTimeTape
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12500000

def emitZeros : ℕ→Meter (List Bool)
  | 0 => ⟨[],1⟩
  | k+1 =>
    let Z := emitZeros k
    ⟨false::Z.result,Z.steps+4⟩

theorem emitted_zeros_exact (q : ℕ) :
    (emitZeros q).result=List.replicate q false ∧ (emitZeros q).steps=4*q+1 := by
  induction q with
  | zero => exact ⟨rfl,rfl⟩
  | succ q ih =>
    simp only [emitZeros,ih.1,ih.2,List.replicate_succ,Nat.mul_succ]
    constructor
    · trivial
    · trivial

def emitOneHot : ℕ→ℕ→Meter (List Bool)
  | 0,_ => ⟨[],1⟩
  | k+1,0 =>
    let Z := emitZeros k
    ⟨true::Z.result,Z.steps+4⟩
  | k+1,j+1 =>
    let Z := emitOneHot k j
    ⟨false::Z.result,Z.steps+4⟩

theorem emitted_one_hot_exact (q j : ℕ) :
    (emitOneHot q j).result=dyadicBits q j ∧ (emitOneHot q j).steps=4*q+1 := by
  induction q generalizing j with
  | zero => exact ⟨rfl,rfl⟩
  | succ q ih =>
    cases j with
    | zero =>
      obtain ⟨h,f⟩ := emitted_zeros_exact q
      simp only [emitOneHot,dyadicBits,h,f,Nat.mul_succ]
      constructor
      · trivial
      · trivial
    | succ j =>
      obtain ⟨h,f⟩ := ih j
      simp only [emitOneHot,dyadicBits,h,f,Nat.mul_succ]
      constructor
      · trivial
      · trivial

def makeCopyWord (m q : ℕ) : Meter (Word q) :=
  let R := emitOneHot q (524184*b m)
  ⟨⟨R.result,by
     rw [(emitted_one_hot_exact _ _).1,dyadicBits_len]⟩,R.steps+3⟩

theorem copy_word_exact (m q : ℕ) (fit : K m<2^q) :
    (makeCopyWord m q).result.val=K m ∧
      (makeCopyWord m q).steps=4*q+4 := by
  have bit : 524184*b m<q := by
    by_contra h
    have K := Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) (Nat.le_of_not_gt h)
    exact (not_le_of_gt fit) K
  obtain ⟨w,c⟩ := emitted_one_hot_exact q (524184*b m)
  constructor
  · change bitsValue (emitOneHot q (524184*b m)).result=K m
    rw [w,dyadicBits_value,if_pos bit,K]
  · change (emitOneHot q (524184*b m)).steps+3=_
    rw [c]

def retainAtWidth {s : ℕ} (q : ℕ) (src : Word s) : Meter (Word q) :=
  let R := scanWidth q src.bits
  ⟨⟨R.result,(congrArg List.length (scanWidth_exact q src.bits).1).trans (lowBits_len q src.bits)⟩,
    R.steps+2*s+4⟩

theorem retain_at_width_exact {s : ℕ} (q : ℕ) (src : Word s) (fit : src.val<2^q) :
    (retainAtWidth q src).result.val=src.val ∧
      (retainAtWidth q src).steps=2*s+4*q+5 := by
  obtain ⟨w,c⟩ := scanWidth_exact q src.bits
  constructor
  · change bitsValue (scanWidth q src.bits).result=src.val
    rw [w,lowBits_value]
    exact Nat.mod_eq_of_lt fit
  · change (scanWidth q src.bits).steps+2*s+4=_
    rw [c]
    omega

structure ExteriorRegisters (q birthWidth : ℕ) where
  copies : Word q
  pre : Word q
  birth : Word birthWidth

def makeExteriorRegisters {s : ℕ} (m q birthWidth : ℕ) (precision : Word s) :
    Meter (ExteriorRegisters q birthWidth) :=
  let C := makeCopyWord m q
  let P := retainAtWidth q precision
  let B := retainAtWidth birthWidth precision
  ⟨⟨C.result,P.result,B.result⟩,C.steps+P.steps+B.steps+8⟩

def exteriorRegistersFee (s q prec : ℕ) : ℕ := 4*s+8*q+4*prec+22

theorem made_exterior_registers_exact {s : ℕ} (m base q prec : ℕ)
    (precision : Word s) (retained : precision.val=J6SourcePrecision.printed m base)
    (cpyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    let R := makeExteriorRegisters m q prec precision
    R.result.copies.val=K m ∧ R.result.pre.val=J6SourcePrecision.printed m base ∧
      R.result.birth.val=J6SourcePrecision.printed m base ∧
      R.steps=exteriorRegistersFee s q prec := by
  obtain ⟨rc,fc⟩ := copy_word_exact m q cpyFit
  obtain ⟨rp,fp⟩ := retain_at_width_exact q precision (by rwa [retained])
  obtain ⟨rb,fb⟩ := retain_at_width_exact prec precision (by rwa [retained])
  refine ⟨rc,rp.trans retained,rb.trans retained,?_⟩
  change (makeCopyWord m q).steps+(retainAtWidth q precision).steps+(retainAtWidth prec precision).steps+8=_
  rw [fc,fp,fb,exteriorRegistersFee]
  omega

theorem made_exterior_registers_have_code_fit {s r c d : ℕ}
    (m base q prec : ℕ) (precision : Word s) (retained : precision.val=J6SourcePrecision.printed m base)
    (cpyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) (raw : List (SignedHalfPort r c d)) :
    let R := makeExteriorRegisters m q prec precision
    1+(writeResidents m (show 0<q from (copy_width_above_one cpyFit).trans' (by decide))
      (oddAxis m) R.result.copies R.result.pre raw).result.roster.modes.length<2^rootCodeWidth m base := by
  obtain ⟨C,P,_,_⟩ := made_exterior_registers_exact m base q prec precision retained cpyFit preFit birthFit
  exact printed_root_code_fit m base _ (copy_width_above_one cpyFit) _ _ C P raw

#print axioms emitted_zeros_exact
#print axioms emitted_one_hot_exact
#print axioms copy_word_exact
#print axioms retain_at_width_exact
#print axioms made_exterior_registers_exact
#print axioms made_exterior_registers_have_code_fit
end J6R52FreshExterior
