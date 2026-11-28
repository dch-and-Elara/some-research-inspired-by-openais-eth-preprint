import J6R27PrescribedProbeRead
import J6R33OriginalJ6ZeroMenu

/-! The existing paid little-endian word encoding and the new
standard choice use exactly the same bit at each ordinal. The
statement does not mention or identify the old chosenRep order. -/
namespace J6R110CanonicalBitsAgreement
open AOracleMachineTimeTape J6R27PrescribedProbe J6R33OriginalJ6

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem encodeBits_eq_testBits (e x : ℕ) :
    encodeBits e x=List.ofFn (fun i : Fin e=>Nat.testBit x i.val) := by
  induction e generalizing x with
  | zero=>rfl
  | succ e ih=>
    simp only [encodeBits,List.ofFn_succ,Fin.val_zero,Fin.val_succ,
      Nat.testBit_zero,Nat.testBit_succ,ih]

theorem bitAt_eq_testBit (e x : ℕ) (i : Fin e) :
    bitAt e x i=Nat.testBit x i.val := by
  have word := bit_word_exact e x
  change List.ofFn (bitAt e x)=encodeBits e x at word
  exact congrFun (List.ofFn_inj.mp (word.trans (encodeBits_eq_testBits e x))) i

theorem zeroPrefix_eq_testBit (e d : ℕ) (i : Fin (d+1)) :
    zeroPrefix e d i=fun k : Fin e=>Nat.testBit i.val k.val :=
  funext (bitAt_eq_testBit e i.val)

theorem zeroPrefix_row_eq_testBits (e d : ℕ) (i : Fin (d+1)) :
    List.ofFn (zeroPrefix e d i)=List.ofFn (fun k : Fin e=>Nat.testBit i.val k.val) :=
  congrArg List.ofFn (zeroPrefix_eq_testBit e d i)

#print axioms encodeBits_eq_testBits
#print axioms bitAt_eq_testBit
#print axioms zeroPrefix_eq_testBit
#print axioms zeroPrefix_row_eq_testBits
end J6R110CanonicalBitsAgreement
