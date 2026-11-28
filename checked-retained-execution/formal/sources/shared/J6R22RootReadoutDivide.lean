
import J6R22RootReadoutWord

/-! Positive exact divisor removal by the actual restoring bit divider.
The signed quotient is never an input and no integer divide operation
occurs in the executable. -/
namespace J6R22RootReadout
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AAcquisitionCost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000

theorem feed_append (a b : List Bool) (t : ℕ) :
    feedValue (a++b) t = feedValue b (feedValue a t) := by
  induction a generalizing t with
  | nil => rfl
  | cons c cs ih => exact ih (2*t+bitNat c)

theorem reverse_feed (input : List Bool) : feedValue input.reverse 0=wordNat input := by
  induction input with
  | nil => rfl
  | cons b bits ih =>
    rw [List.reverse_cons,feed_append,ih]
    change 2*wordNat bits+bitNat b=bitNat b+2*wordNat bits
    omega

theorem quotient_trace_length (d bits : List Bool) (init : List Bool×List Bool) :
    (divisionDigits d bits init).1.length=init.1.length+bits.length := by
  induction bits generalizing init with
  | nil => simp [divisionDigits]
  | cons b bs ih =>
    let r := divideDigit d init.2 b
    change (divisionDigits d bs (r.1::init.1,r.2)).1.length=_
    rw [ih]
    simp only [List.length_cons]
    omega

theorem binary_divide_length (d msbBits : List Bool) :
    (binaryDivide d msbBits).length=msbBits.length := by
  unfold binaryDivide
  rw [quotient_trace_length]
  simp

def signedDivisionFee (numWidth denWidth : ℕ) : ℕ :=
  16*numWidth*(2*denWidth+5)+3*numWidth+3*denWidth+8

def divideMagnitude {p b : ℕ} (x : A1R10.Word p) (d : A1R10.Word b) :
    Meter (A1R10.Word p) :=
  let q := binaryDivide d.val x.val.reverse
  ⟨⟨q,by simp only [q,binary_divide_length,List.length_reverse,x.property]⟩,
    16*divisionSchedule x.val.reverse d.val+3*x.val.length+3*d.val.length+8⟩

theorem divide_magnitude_exact {p b : ℕ} (x : A1R10.Word p) (d : A1R10.Word b)
    (hd : 0<bitsValue d.val) :
    bitsValue (divideMagnitude x d).result.val=bitsValue x.val/bitsValue d.val ∧
      (divideMagnitude x d).steps=signedDivisionFee p b := by
  constructor
  · change bitsValue (binaryDivide d.val x.val.reverse)=_
    rw [← little_endian_same,binaryDivide_exact _ _ (by rwa [little_endian_same]),
      reverse_feed,little_endian_same x.val,little_endian_same d.val]
  · change 16*divisionSchedule x.val.reverse d.val+3*x.val.length+3*d.val.length+8=_
    simp only [divisionSchedule,List.length_reverse,x.property,d.property,signedDivisionFee]
    ring

def divideSigned {p b : ℕ} (x : SignedMagnitude p) (factor : A1R10.Word b) :
    Meter (SignedMagnitude p) :=
  let q := divideMagnitude x.magnitude factor
  ⟨⟨x.negative,q.result⟩,q.steps+2⟩

theorem divide_signed_exact_factor {p b : ℕ} (x : SignedMagnitude p) (factor : A1R10.Word b)
    (hd : 0<bitsValue factor.val) (y : ℤ) (fit : x.value=(bitsValue factor.val:ℤ)*y) :
    (divideSigned x factor).result.value=y ∧
      (divideSigned x factor).steps=signedDivisionFee p b+2 := by
  let absDiv := divideMagnitude x.magnitude factor
  let D := bitsValue factor.val
  have Dpos : (0:ℤ)<(D:ℤ) := by exact_mod_cast hd
  have hn : x.value.natAbs=bitsValue x.magnitude.val := by
    unfold SignedMagnitude.value signedDenote
    cases x.negative <;> simp
  have mag : bitsValue x.magnitude.val=D*y.natAbs := by
    rw [← hn,fit,Int.natAbs_mul,Int.natAbs_natCast]
  obtain ⟨out,steps⟩ := divide_magnitude_exact x.magnitude factor hd
  change bitsValue absDiv.result.val=bitsValue x.magnitude.val/D at out
  have out' : bitsValue absDiv.result.val=y.natAbs := by
    rw [out,mag,Nat.mul_comm D y.natAbs,Nat.mul_div_cancel _ (show 0<D from hd)]
  constructor
  · apply mul_left_cancel₀ Dpos.ne'
    rw [← fit]
    unfold divideSigned SignedMagnitude.value signedDenote
    change (D:ℤ)*(if x.negative then -(bitsValue absDiv.result.val:ℤ) else bitsValue absDiv.result.val)=
      (if x.negative then -(bitsValue x.magnitude.val:ℤ) else bitsValue x.magnitude.val)
    rw [out',mag]
    cases x.negative <;> simp
  · change (divideMagnitude x.magnitude factor).steps+2=_
    rw [steps]

def clearThenDivide {p b : ℕ} (hp : 0<p) (den z : A1R10.Word p)
    (clock : List Unit) (D : A1R10.Word b) : Meter (SignedMagnitude p) :=
  let a := clearAndCenter hp den z clock
  let b := divideSigned a.result D
  ⟨b.result,a.steps+b.steps+2⟩

theorem clear_then_divide_exact {p b : ℕ} (hp : 0<p) (den z : A1R10.Word p)
    (clock : List Unit) (D : A1R10.Word b) (hD : 0<bitsValue D.val) (truth : ℤ)
    (fit : ((wordRead den)^clock.length*wordRead z).valMinAbs=(bitsValue D.val:ℤ)*truth) :
    (clearThenDivide hp den z clock D).result.value=truth ∧
      (clearThenDivide hp den z clock D).steps≤38*p+20+(clock.length+1)*wordMulFee p+
        signedDivisionFee p b := by
  obtain ⟨r,c⟩ := clear_and_center_exact hp den z clock
  obtain ⟨o,h⟩ := divide_signed_exact_factor _ D hD truth (r.trans fit)
  refine ⟨o,?_⟩
  change (clearAndCenter hp den z clock).steps+
    (divideSigned (clearAndCenter hp den z clock).result D).steps+2≤_
  omega

#print axioms reverse_feed
#print axioms binary_divide_length
#print axioms divide_magnitude_exact
#print axioms divide_signed_exact_factor
#print axioms clear_then_divide_exact
end J6R22RootReadout
