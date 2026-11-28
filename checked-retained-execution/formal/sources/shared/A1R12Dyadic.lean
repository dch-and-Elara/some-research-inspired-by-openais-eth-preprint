import A1R12Words

/-! Signed dyadic normalization directly on little-endian magnitude
bits. Strip literal zero bits; cast only the resulting odd suffix to
Z/(2^p). This handles negative differences and the source's zero
convention exactly, without calling padicValInt or integer division. -/

namespace A1R12
open A1R10 AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open P1DyadicGrid AOracleSuccinctNative

def stripZeros : List Bool → List Unit × List Bool
  | [] => ([],[])
  | true::xs => ([],true::xs)
  | false::xs =>
    let q := stripZeros xs
    (()::q.1,q.2)

theorem stripZeros_exact (l : List Bool) :
    bitsValue l = 2^(stripZeros l).1.length * bitsValue (stripZeros l).2 ∧
      ((stripZeros l).2=[] ∨ Odd (bitsValue (stripZeros l).2)) := by
  induction l with
  | nil => simp [stripZeros,bitsValue]
  | cons b bs ih =>
    cases b
    · change bitsValue (false::bs)=2^((stripZeros bs).1.length+1)*bitsValue (stripZeros bs).2 ∧ _
      refine ⟨?_,ih.2⟩
      rw [bitsValue,ih.1,pow_succ,Bool.toNat_false]
      ring
    · refine ⟨by simp [stripZeros], Or.inr ?_⟩
      exact ⟨bitsValue bs,by simp only [stripZeros,bitsValue,Bool.toNat_true]; omega⟩

theorem signedDenote_strip (l : List Bool) (sgn : Bool) :
    signedDenote sgn l = pow₂ (stripZeros l).1.length * signedDenote sgn (stripZeros l).2 := by
  have h := congrArg (fun n : ℕ => (n:ℤ)) (stripZeros_exact l).1
  push_cast at h
  cases sgn <;> simp [signedDenote,pow₂,h,mul_neg]

def dyadicNormalize {p : ℕ} (hp : 0<p) (sgn : Bool) (l : List Bool) :
    Meter (ℕ × A1R10.Word p) :=
  let q := stripZeros l
  let v := signedWord hp sgn q.2
  let level := if q.2.isEmpty then 0 else q.1.length
  ⟨(level,v.result),v.steps+6*(l.length+1)^2+4⟩

theorem dyadicNormalize_exact {p : ℕ} (hp : 0<p) (sgn : Bool) (l : List Bool) :
    (dyadicNormalize hp sgn l).result.1=padicValInt 2 (signedDenote sgn l) ∧
    wordRead (dyadicNormalize hp sgn l).result.2=(oddWord (signedDenote sgn l):ZMod (2^p)) ∧
    (dyadicNormalize hp sgn l).steps≤19*p+10+6*(l.length+1)^2 := by
  let q := stripZeros l
  obtain ⟨ha,hc⟩ := signedWord_exact hp sgn q.2
  have h := signedDenote_strip l sgn
  change signedDenote sgn l=pow₂ q.1.length*signedDenote sgn q.2 at h
  refine ⟨?_,?_,?_⟩
  · change (if q.2.isEmpty then 0 else q.1.length)=_
    by_cases he : q.2=[]
    · have hz : signedDenote sgn []=0 := by cases sgn <;> simp [signedDenote,bitsValue]
      rw [he,hz,mul_zero] at h
      simp [he,h]
    · have hor : Odd (bitsValue q.2) := (stripZeros_exact l).2.resolve_left he
      have hOdd : Odd (signedDenote sgn q.2) := by
        have hh : Odd (bitsValue q.2:ℤ) := by exact_mod_cast hor
        cases sgn <;> simp [signedDenote,hh]
      rw [h,valuation_pow₂_mul_odd q.1.length hOdd]
      simp [he]
  · change wordRead (signedWord hp sgn q.2).result=_
    rw [ha]
    by_cases he : q.2=[]
    · rw [he] at h
      simp [signedDenote,bitsValue] at h
      simp [he,h,signedDenote,bitsValue,oddWord]
    · have hor : Odd (bitsValue q.2) := (stripZeros_exact l).2.resolve_left he
      have hOdd : Odd (signedDenote sgn q.2) := by
        have hh : Odd (bitsValue q.2:ℤ) := by exact_mod_cast hor
        cases sgn <;> simp [signedDenote,hh]
      have hLevel := valuation_pow₂_mul_odd q.1.length hOdd
      unfold oddWord
      rw [h,hLevel,Int.mul_ediv_cancel_left _ (pow₂_pos _).ne']
  · change (signedWord hp sgn q.2).steps+6*(l.length+1)^2+4≤_
    omega

#print axioms stripZeros_exact
#print axioms signedDenote_strip
#print axioms dyadicNormalize_exact
end A1R12

