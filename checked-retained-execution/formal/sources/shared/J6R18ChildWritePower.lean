import A1R12Combine

/-! Literal repeated squaring from little-endian exponent bytes. This
charges the finite quadratic UV arithmetic at each consumed bit, not
a black-box exponentiation gate or a free arbitrary-precision scalar. -/
namespace J6R18ChildWrite
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open A1R10 A1R11 A1R12

def powBits {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) :
    List Bool → UVBlock fw ell → Meter (UVBlock fw ell)
  | [],_ => oneM hp he hv
  | bit::tail,x =>
    let sq := uvMul hp x x
    let u := powBits hp he hv tail sq.result
    let v := if bit then uvMul hp x u.result else Meter.pure u.result
    ⟨v.result,sq.steps+u.steps+v.steps+3*uvWidth fw.length ell p+12⟩

def powBitCap (e ell p b : ℕ) :=
  uvWidth e ell p+b*(2*mulCap e ell p+3*uvWidth e ell p+12)

theorem powBits_exact {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (bits : List Bool) (x : UVBlock fw ell) :
    let z := powBits hp he hv bits x
    uvRead hp fw ell z.result=(uvRead hp fw ell x)^(bitsValue bits) ∧
      z.steps≤powBitCap fw.length ell p bits.length := by
  induction bits generalizing x with
  | nil => simp [powBits,powBitCap,bitsValue,oneM,uvOne_read]
  | cons bit bits ih =>
    let s := uvMul hp x x
    let u := powBits hp he hv bits s.result
    let v := uvMul hp x u.result
    let W := uvWidth fw.length ell p
    let M := mulCap fw.length ell p
    let N := powBitCap fw.length ell p bits.length
    have hU := ih s.result
    change uvRead hp fw ell u.result=_ ∧ u.steps≤N at hU
    obtain ⟨hS,hSC⟩ := uvMul_native_bit_cost hp x x
    obtain ⟨hV,hVC⟩ := uvMul_native_bit_cost hp x u.result
    have heq : uvRead hp fw ell u.result=(uvRead hp fw ell x)^(2*bitsValue bits) := by
      rw [hU.1,show uvRead hp fw ell s.result=_ from hS,← pow_two,← pow_mul]
    have hc : powBitCap fw.length ell p (bit::bits).length=N+(2*M+3*W+12) := by
      unfold N W M powBitCap
      rw [List.length_cons,Nat.succ_mul]
      omega
    change s.steps≤M at hSC
    change v.steps≤M at hVC
    cases bit
    · change uvRead hp fw ell u.result=(uvRead hp fw ell x)^(bitsValue (false::bits)) ∧
        s.steps+u.steps+0+3*W+12≤powBitCap fw.length ell p (false::bits).length
      simp only [bitsValue,Bool.toNat_false,zero_add,heq,true_and,hc]
      omega
    · change uvRead hp fw ell v.result=(uvRead hp fw ell x)^(bitsValue (true::bits)) ∧
        s.steps+u.steps+v.steps+3*W+12≤powBitCap fw.length ell p (true::bits).length
      change uvRead hp fw ell v.result=_ at hV
      simp only [bitsValue,Bool.toNat_true,hV,heq,pow_add,pow_one,hc,true_and]
      omega

#print axioms powBits_exact
end J6R18ChildWrite

