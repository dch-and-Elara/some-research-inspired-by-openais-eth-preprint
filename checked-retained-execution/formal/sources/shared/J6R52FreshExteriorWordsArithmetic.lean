import J6R52FreshExteriorWordsRetained
import J6R22RootReadoutDivide

/-! Synthesize the printed precision from the public mesh dimensions
and an actual base-precision bit word. The nontrivial ceiling uses
the proved restoring binary divider (not an integer-valued oracle).
Natural m only sets public loop lengths and mesh exponents. -/
namespace J6R52FreshExterior
open scoped Classical
open J6Mesh J6R19Retained J6R22RootReadout A1R10 A1R12
open AOracleMachineTime AOracleMachineTimeTape
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 15000000
set_option maxRecDepth 2700

def constantRegister (q : ℕ) (raw : List Bool) : Meter (A1R10.Word q) :=
  let R := scanWidth q raw
  ⟨⟨R.result,(congrArg List.length (scanWidth_exact q raw).1).trans (lowBits_len q raw)⟩,
    R.steps+3⟩

theorem constant_register_read (q : ℕ) (raw : List Bool) :
    wordRead (constantRegister q raw).result=(bitsValue raw:ZMod (2^q)) := by
  change (bitsValue (scanWidth q raw).result:ZMod (2^q))=_
  rw [(scanWidth_exact q raw).1,lowBits_value,ZMod.natCast_mod]

def powerRegister (q j : ℕ) : Meter (A1R10.Word q) :=
  let R := emitOneHot q j
  ⟨⟨R.result,(congrArg List.length (emitted_one_hot_exact q j).1).trans (dyadicBits_len q j)⟩,
    R.steps+3⟩

theorem power_register_read (q j : ℕ) :
    wordRead (powerRegister q j).result=(2:ZMod (2^q))^j := by
  rw [show (powerRegister q j).result=dyadicWord q j from Subtype.ext (emitted_one_hot_exact q j).1]
  exact dyadicWord_read q j

def timesAddRegister {q : ℕ} (seed step : A1R10.Word q) : ℕ→Meter (A1R10.Word q)
  | 0 => ⟨seed,2⟩
  | k+1 =>
    let R := timesAddRegister seed step k
    let A := addWord R.result step
    ⟨A.result,R.steps+A.steps+5⟩

theorem times_add_register_read {q : ℕ} (seed step : A1R10.Word q) (k : ℕ) :
    wordRead (timesAddRegister seed step k).result=wordRead seed+(k:ZMod (2^q))*wordRead step := by
  induction k with
  | zero => simp [timesAddRegister]
  | succ k ih =>
    dsimp only [timesAddRegister]
    rw [addWord_read,ih,Nat.cast_succ]
    ring

structure GeometryRegisters (q : ℕ) where
  divisor : A1R10.Word q
  offset : A1R10.Word q
  slope : A1R10.Word q
  whole : A1R10.Word q
  length : A1R10.Word q
  three : A1R10.Word q
  eight : A1R10.Word q

def printedGeometryRegisters (m q : ℕ) : Meter (GeometryRegisters q) :=
  let zero := constantRegister q []
  let one := constantRegister q [true]
  let three := constantRegister q [true,true]
  let four := constantRegister q [false,false,true]
  let eight := constantRegister q [false,false,false,true]
  let Q := timesAddRegister zero.result four.result (b m)
  let R := timesAddRegister three.result four.result (b m-1)
  let S := timesAddRegister one.result eight.result (b m)
  let W := powerRegister q (lambda m)
  let L := powerRegister q (a m)
  ⟨⟨Q.result,R.result,S.result,W.result,L.result,three.result,eight.result⟩,
    zero.steps+one.steps+three.steps+four.steps+eight.steps+
      Q.steps+R.steps+S.steps+W.steps+L.steps+12⟩

theorem printed_geometry_registers_read (m q : ℕ) :
    let R := (printedGeometryRegisters m q).result
    wordRead R.divisor=(u m:ZMod (2^q)) ∧
      wordRead R.offset=(u m-1:ℕ) ∧ wordRead R.slope=(a m+1:ℕ) ∧
      wordRead R.whole=(M m:ℕ) ∧ wordRead R.length=(L m:ℕ) ∧
      wordRead R.three=3 ∧ wordRead R.eight=8 := by
  have hB := b_pos m
  have hU : 4*(b m-1)+3=u m-1 := by unfold u; omega
  have Z : wordRead (constantRegister q []).result=(0:ZMod (2^q)) := by
    norm_num [constant_register_read,bitsValue]
  have O : wordRead (constantRegister q [true]).result=(1:ZMod (2^q)) := by
    norm_num [constant_register_read,bitsValue,Bool.toNat]
  have T : wordRead (constantRegister q [true,true]).result=(3:ZMod (2^q)) := by
    norm_num [constant_register_read,bitsValue,Bool.toNat]
  have F : wordRead (constantRegister q [false,false,true]).result=(4:ZMod (2^q)) := by
    norm_num [constant_register_read,bitsValue,Bool.toNat]
  have E : wordRead (constantRegister q [false,false,false,true]).result=(8:ZMod (2^q)) := by
    norm_num [constant_register_read,bitsValue,Bool.toNat]
  dsimp only [printedGeometryRegisters]
  refine ⟨?_,?_,?_,?_,?_,T,E⟩
  · rw [times_add_register_read,Z,F]
    unfold u
    push_cast
    ring
  · rw [times_add_register_read,T,F,←hU]
    push_cast
    ring
  · rw [times_add_register_read,O,E]
    unfold a
    push_cast
    ring
  · rw [power_register_read,M,Nat.cast_pow]; norm_num
  · rw [power_register_read,L,Nat.cast_pow]; norm_num

theorem native_divider_ranges (m base : ℕ) :
    0<u m ∧ u m≤J6SourcePrecision.printed m base ∧
      3*M m+(u m-1)≤J6SourcePrecision.printed m base := by
  have bpos := b_pos m
  have E : u m≤lambda m := by unfold u lambda; omega
  have BM : u m≤M m := E.trans (show lambda m<2^lambda m from Nat.lt_two_pow_self).le
  have p : 8*M m≤J6SourcePrecision.printed m base := by
    have mul := Nat.mul_le_mul_left (8*M m) (show 1≤a m+1 by omega)
    simp only [Nat.mul_one] at mul
    unfold J6SourcePrecision.printed
    omega
  exact ⟨by unfold u; omega,by omega,by omega⟩

theorem exact_nat_of_register_read {q n : ℕ} (x : A1R10.Word q)
    (fit : n<2^q) (eq : wordRead x=(n:ZMod (2^q))) :
    bitsValue x.val=n := by
  have h := congrArg ZMod.val eq
  rw [wordLeast,ZMod.val_natCast,Nat.mod_eq_of_lt fit] at h
  exact h

def precisionFromBaseWord {q : ℕ} (m : ℕ) (base : A1R10.Word q) :
    Meter (A1R10.Word q) :=
  let G := printedGeometryRegisters m q
  let N₀ := mulWord G.result.three G.result.whole
  let N := addWord N₀.result G.result.offset
  let H := divideMagnitude N.result G.result.divisor
  let A₀ := mulWord G.result.eight H.result
  let A := mulWord A₀.result G.result.length
  let B₀ := mulWord G.result.eight G.result.whole
  let B := mulWord B₀.result G.result.slope
  let T := addWord A.result B.result
  let R := addWord base T.result
  ⟨R.result,G.steps+N₀.steps+N.steps+H.steps+A₀.steps+A.steps+
    B₀.steps+B.steps+T.steps+R.steps+16⟩

theorem precision_from_base_word_exact {q : ℕ} (m base : ℕ) (baseWord : A1R10.Word q)
    (orig : bitsValue baseWord.val=base) (fit : J6SourcePrecision.printed m base<2^q) :
    bitsValue (precisionFromBaseWord m baseWord).result.val=J6SourcePrecision.printed m base := by
  let G := printedGeometryRegisters m q
  let N₀ := mulWord G.result.three G.result.whole
  let N := addWord N₀.result G.result.offset
  let H := divideMagnitude N.result G.result.divisor
  obtain ⟨u',k,a',M',L',three,eight⟩ := printed_geometry_registers_read m q
  obtain ⟨upos,ufit,nfit⟩ := native_divider_ranges m base
  have D : bitsValue G.result.divisor.val=u m := exact_nat_of_register_read _ (ufit.trans_lt fit) u'
  have num : wordRead N.result=((3*M m+(u m-1):ℕ):ZMod (2^q)) := by
    change wordRead (addWord (mulWord G.result.three G.result.whole).result G.result.offset).result=_
    rw [addWord_read,mulWord_read,three,M',k,Nat.cast_add,Nat.cast_mul]
    norm_num
  have Nv := exact_nat_of_register_read N.result (nfit.trans_lt fit) num
  have X := (divide_magnitude_exact N.result G.result.divisor (by rwa [D])).1
  change bitsValue H.result.val=(_ / _) at X
  rw [D,Nv] at X
  have nc : 3*M m+(u m-1)=3*M m+u m-1 := by omega
  rw [nc] at X
  have R : wordRead H.result=(J6SourcePrecision.h m:ZMod (2^q)) := by
    change (bitsValue H.result.val:ZMod (2^q))=_
    rw [X,J6SourcePrecision.h]
  have O : wordRead baseWord=(base:ZMod (2^q)) := by
    change (bitsValue baseWord.val:ZMod (2^q))=_
    rw [orig]
  apply exact_nat_of_register_read _ fit
  change wordRead (addWord baseWord (addWord
    (mulWord (mulWord G.result.eight H.result).result G.result.length).result
    (mulWord (mulWord G.result.eight G.result.whole).result G.result.slope).result).result).result=_
  rw [addWord_read,addWord_read,mulWord_read,mulWord_read,mulWord_read,mulWord_read,O,eight,R,L',M',a']
  unfold J6SourcePrecision.printed
  push_cast
  ring

#print axioms constant_register_read
#print axioms power_register_read
#print axioms times_add_register_read
#print axioms printed_geometry_registers_read
#print axioms native_divider_ranges
#print axioms exact_nat_of_register_read
#print axioms precision_from_base_word_exact
end J6R52FreshExterior
