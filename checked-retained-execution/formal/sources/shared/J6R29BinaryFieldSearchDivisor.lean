
import J6R28GeneratedRootFrameBits
import A1R10Monic

/-! The source's original binary monic division trial uses actual
one-bit coefficient words. A paired tape walk builds the unary
quotient-step clock; the finite reduction is the audited monic worker.
No arithmetic over an unpriced abstract field is used by this test. -/
namespace J6R29BinaryFieldSearch
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime AOracleMachineTimeMul
open J6R28GeneratedRootFrame
set_option maxHeartbeats 5500000
set_option maxRecDepth 1200

abbrev binaryOps := wordOps 1 (by decide : 0<(1:ℕ))

def quotientClock : List Bool→List Bool→Meter (List Unit)
  | [],_ => ⟨[],3⟩
  | _::xs,[] =>
    let c := quotientClock xs []
    ⟨()::c.result,c.steps+6⟩
  | _::xs,_::ys =>
    let c := quotientClock xs ys
    ⟨c.result,c.steps+6⟩

theorem quotient_clock_exact (x y : List Bool) :
    (quotientClock x y).result.length=x.length-y.length ∧
      (quotientClock x y).steps=3+6*x.length := by
  induction x generalizing y with
  | nil => simp [quotientClock]
  | cons b xs ih =>
    cases y with
    | nil =>
      obtain ⟨l,c⟩ := ih []
      refine ⟨by simpa [quotientClock] using congrArg Nat.succ l,?_⟩
      change (quotientClock xs []).steps+6=3+6*(xs.length+1)
      rw [c,Nat.mul_add,Nat.mul_one]
      omega
    | cons z ys =>
      obtain ⟨l,c⟩ := ih ys
      refine ⟨by simpa [quotientClock] using l,?_⟩
      change (quotientClock xs ys).steps+6=3+6*(xs.length+1)
      rw [c,Nat.mul_add,Nat.mul_one]
      omega

def reduceByClock (g : List (Word 1)) : List Unit→List (Word 1)→Meter (List (Word 1))
  | [],v => ⟨v,0⟩
  | _::_,[] => ⟨[],0⟩
  | _::s,x::xs =>
    let a := subtractScaled binaryOps.toGates x g xs
    let b := reduceByClock g s a.result
    ⟨b.result,a.steps+b.steps+4*(binaryOps.move+1)⟩

theorem reduce_by_clock (g : List (Word 1)) (s : List Unit) (v : List (Word 1)) :
    reduceByClock g s v=A1R10.reduce binaryOps.toGates g s.length v := by
  induction s generalizing v with
  | nil => rfl
  | cons tok ts ih =>
    cases v <;> simp only [reduceByClock,A1R10.reduce,List.length_cons,ih]

theorem one_bit_word_zero (x : Word 1) :
    x.val.headD false=false ↔ wordRead x=0 := by
  obtain ⟨xs,len⟩ := x
  rcases xs with _|⟨b,bs⟩
  · simp at len
  · have hLen : bs.length+1=0+1 := len
    have hnil : bs=[] := List.eq_nil_of_length_eq_zero (Nat.add_right_cancel hLen)
    subst bs
    cases b <;> simp [wordRead,asResidue,bitsValue]

def checkZeroWords : List (Word 1)→Meter Bool
  | [] => ⟨true,3⟩
  | x::xs =>
    let a := checkZeroWords xs
    ⟨!x.val.headD false && a.result,a.steps+6⟩

theorem check_zero_words_exact (xs : List (Word 1)) :
    ((checkZeroWords xs).result=true ↔ decode binaryOps xs=0) ∧
      (checkZeroWords xs).steps=3+6*xs.length := by
  induction xs with
  | nil => simp [checkZeroWords,decode]
  | cons x xs ih =>
    constructor
    · change (!x.val.headD false && (checkZeroWords xs).result)=true ↔ _
      rw [Bool.and_eq_true,Bool.not_eq_true',one_bit_word_zero,ih.1]
      change wordRead x=0 ∧ decode binaryOps xs=0 ↔
        monomial xs.length (wordRead x)+decode binaryOps xs=0
      constructor
      · rintro ⟨h,z⟩
        simp [h,z]
      · intro H
        have coeff := congrArg (fun P : (ZMod (2^1))[X]=>P.coeff xs.length) H
        change (monomial xs.length (wordRead x)+decode binaryOps xs).coeff xs.length =
          (0 : (ZMod (2^1))[X]).coeff xs.length at coeff
        rw [coeff_add,decode_coeff_zero binaryOps xs xs.length le_rfl,add_zero,coeff_zero] at coeff
        have z : wordRead x=0 := (coeff_monomial_same xs.length (wordRead x)).symm.trans coeff
        refine ⟨z,?_⟩
        rw [z,monomial_zero_right,zero_add] at H
        exact H
    · change (checkZeroWords xs).steps+6=3+6*(xs.length+1)
      rw [ih.2,Nat.mul_add,Nat.mul_one]
      omega

def binaryDivisorTest (f g : List Bool) : Meter Bool :=
  let A := widenLower 1 f
  let B := widenLower 1 g
  let W := quotientClock (true::f) g
  let rem := reduceByClock B.result W.result (zeroExtend 1 true::A.result)
  let Z := checkZeroWords rem.result
  ⟨Z.result,A.steps+B.steps+W.steps+rem.steps+Z.steps+8⟩

def divisorTrialFee (e d : ℕ) : ℕ :=
  (4+10*e)+(4+10*d)+(3+6*(e+1))+(e+1-d)*(d+1)*264+(3+6*d)+8

theorem binary_divisor_trial (f g : List Bool) (hd : 0<g.length) (hfit : g.length≤f.length+1) :
    ((binaryDivisorTest f g).result=true ↔
       binaryPolynomial (ZMod 2) g ∣ binaryPolynomial (ZMod 2) f) ∧
    (binaryDivisorTest f g).steps≤divisorTrialFee f.length g.length := by
  let A := widenLower 1 f
  let B := widenLower 1 g
  let W := quotientClock (true::f) g
  let orig := zeroExtend 1 true::A.result
  let rem := reduceByClock B.result W.result orig
  have aLen : A.result.length=f.length := by rw [(widen_lower_exact 1 f).1,List.length_map]
  have bLen : B.result.length=g.length := by rw [(widen_lower_exact 1 g).1,List.length_map]
  have clock := quotient_clock_exact (true::f) g
  have wLen : W.result.length=f.length+1-g.length := clock.1
  have nFit : orig.length=B.result.length+W.result.length := by
    change A.result.length+1=_
    rw [aLen,bLen,wLen,Nat.add_sub_of_le hfit]
  obtain ⟨jL,jEq,jFee⟩ := reduce_exact binaryOps B.result W.result.length orig nFit
  have len : rem.result.length=g.length := by
    change (reduceByClock B.result W.result orig).result.length=g.length
    rw [reduce_by_clock,jL,bLen]
  have den : modulus binaryOps B.result=binaryPolynomial (ZMod 2) g := by
    change monomial B.result.length 1+decode binaryOps B.result=_
    rw [bLen,show B.result=g.map (zeroExtend 1) from (widen_lower_exact 1 g).1,decode_widened_lower]
    rfl
  have num : decode binaryOps orig=binaryPolynomial (ZMod 2) f := by
    change monomial A.result.length (wordRead (zeroExtend 1 true))+decode binaryOps A.result=_
    rw [aLen,(zero_extend_at_positive 1 (by decide) true).2,
      show A.result=f.map (zeroExtend 1) from (widen_lower_exact 1 f).1,decode_widened_lower]
    rfl
  let remPoly := decode binaryOps rem.result
  have H : AdjoinRoot.mk (binaryPolynomial (ZMod 2) g) remPoly =
      AdjoinRoot.mk (binaryPolynomial (ZMod 2) g) (binaryPolynomial (ZMod 2) f) := by
    change AdjoinRoot.mk (binaryPolynomial (ZMod 2) g)
      (decode binaryOps (reduceByClock B.result W.result orig).result)=_
    rw [reduce_by_clock,←den,←num]
    exact jEq
  have rDegree : remPoly.natDegree<g.length := by
    apply Nat.lt_of_le_of_lt (m:=g.length-1) ?_ (by omega)
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact decode_coeff_zero binaryOps rem.result k (by rw [len]; omega)
  have hTest := check_zero_words_exact rem.result
  constructor
  · change (checkZeroWords rem.result).result=true ↔ _
    rw [hTest.1,←AdjoinRoot.mk_eq_zero,←H]
    constructor
    · intro z
      change remPoly=0 at z
      rw [z,map_zero]
    · intro z
      change remPoly=0
      by_contra bad
      have d := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp z) bad
      rw [(binary_monic_degree (ZMod 2) g).2] at d
      omega
  · have rFee : rem.steps≤(f.length+1-g.length)*(g.length+1)*264 := by
      change (reduceByClock B.result W.result orig).steps≤_
      rw [reduce_by_clock]
      simpa only [bLen,wLen,binaryOps,wordOps] using jFee
    have hA : A.steps=4+10*f.length := by
      simpa [Nat.mul_comm] using (widen_lower_exact 1 f).2
    have hB : B.steps=4+10*g.length := by
      simpa [Nat.mul_comm] using (widen_lower_exact 1 g).2
    have hC : W.steps=3+6*(f.length+1) := clock.2
    have hZ : (checkZeroWords rem.result).steps=3+6*g.length := by rw [hTest.2,len]
    change A.steps+B.steps+W.steps+rem.steps+(checkZeroWords rem.result).steps+8≤_
    rw [hA,hB,hC,hZ,divisorTrialFee]
    omega

#print axioms quotient_clock_exact
#print axioms reduce_by_clock
#print axioms check_zero_words_exact
#print axioms binary_divisor_trial
end J6R29BinaryFieldSearch
