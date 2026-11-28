
import J6R28GeneratedRootFramePoly
import A1R10UV

/-! The physical modulus tape is a one-pass widening of the source
literal binary coefficients. A copied bit is put at the low end, with
real zero writes to fill precisely p bits. -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeMul
set_option maxHeartbeats 2700000

def zeroExtend : (p : ℕ)→Bool→Word p
  | 0,_ => ⟨[],rfl⟩
  | p+1,b => ⟨b::List.replicate p false,by simp⟩

theorem zero_extend_at_positive (p : ℕ) (hp : 0<p) (b : Bool) :
    (zeroExtend p b).val=b::List.replicate (p-1) false ∧
    wordRead (zeroExtend p b)=(if b then 1 else 0 : ZMod (2^p)) := by
  cases p with
  | zero => omega
  | succ p =>
    refine ⟨by simp [zeroExtend],?_⟩
    simp only [zeroExtend,wordRead,asResidue,bitsValue,value_zero,mul_zero,add_zero]
    cases b <;> simp

def widenLower (p : ℕ) : List Bool→Meter (List (Word p))
  | [] => ⟨[],4⟩
  | b::bs =>
    let r := widenLower p bs
    ⟨zeroExtend p b::r.result,r.steps+4*p+6⟩

theorem widen_lower_exact (p : ℕ) (bs : List Bool) :
    (widenLower p bs).result=bs.map (zeroExtend p) ∧
    (widenLower p bs).steps=4+bs.length*(4*p+6) := by
  induction bs with
  | nil => simp [widenLower]
  | cons b bs ih =>
    refine ⟨by simp only [widenLower,List.map_cons,ih.1],?_⟩
    change (widenLower p bs).steps+4*p+6=4+(bs.length+1)*(4*p+6)
    rw [ih.2,Nat.add_mul,one_mul]
    omega

theorem decode_widened_lower (p : ℕ) (hp : 0<p) (bs : List Bool) :
    decode (wordOps p hp) (bs.map (zeroExtend p))=lowerBinary (ZMod (2^p)) bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons,decode,List.length_map,ih,lowerBinary]
    change monomial bs.length (wordRead (zeroExtend p b))+_ = _
    exact congrArg (fun x=>monomial bs.length x+lowerBinary (ZMod (2^p)) bs)
      (zero_extend_at_positive p hp b).2

theorem widened_modulus_exact (p : ℕ) (hp : 0<p) {f : ℤ[X]} (data : LiteralPresentation f) :
    Modulus p hp (widenLower p data.lower).result=NativeProbeRing.liftPoly p f := by
  rw [(widen_lower_exact p data.lower).1]
  change monomial (data.lower.map (zeroExtend p)).length 1+
    decode (wordOps p hp) (data.lower.map (zeroExtend p))=_
  rw [List.length_map,decode_widened_lower]
  change binaryPolynomial (ZMod (2^p)) data.lower=_
  rw [←binary_polynomial_map (Int.castRingHom (ZMod (2^p))),data.exactPolynomial]
  rfl

#print axioms zero_extend_at_positive
#print axioms widen_lower_exact
#print axioms decode_widened_lower
#print axioms widened_modulus_exact
end J6R28GeneratedRootFrame
