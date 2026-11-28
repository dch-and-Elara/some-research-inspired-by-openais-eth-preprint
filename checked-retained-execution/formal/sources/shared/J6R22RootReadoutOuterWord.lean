
import J6R22RootReadoutDivide
import J6R22RootReadoutOuter

/-! Explicit bit-time at the outer polynomial evaluation. The machine
uses the ordinary unreduced common-denominator recurrence and one final
restoring division. Its intermediates are fixed-width words, so arbitrary
integer and rational operations occur only in the proof. -/
namespace J6R22RootReadout
open scoped BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates J9R19CompiledBits
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option maxRecDepth 1536

structure FractionWord (p : ℕ) where
  num : Word p
  den : Word p

def FractionWord.matches {p : ℕ} (w : FractionWord p) (x : Fraction) : Prop :=
  wordRead w.num=(x.num:ZMod (2^p)) ∧ wordRead w.den=(x.den:ZMod (2^p))

def commonPair : List Fraction → Fraction
  | [] => ⟨0,1⟩
  | x::xs =>
    let tail := commonPair xs
    ⟨x.num*tail.den+x.den*tail.num,x.den*tail.den⟩

theorem common_pair_shape (xs : List Fraction) :
    commonPair xs=⟨clearedSpec xs,(dens xs).prod⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [commonPair,ih,clearedSpec,dens,List.map_cons,List.prod_cons]

theorem common_pair_good (xs : List Fraction) (h : ∀ x∈xs,x.good) :
    (commonPair xs).good := by
  induction xs with
  | nil => simp [commonPair,Fraction.good]
  | cons x xs ih =>
    exact mul_ne_zero (h x List.mem_cons_self) (ih (fun y hy=>h y (List.mem_cons_of_mem _ hy)))

theorem common_pair_value (xs : List Fraction) (h : ∀ x∈xs,x.good) :
    (commonPair xs).value=(clearRun xs).result.value := by
  rw [common_pair_shape,clearedSpec_exact xs h,clearRun_exact xs h]

theorem common_pair_fits (xs : List Fraction) (b : ℕ) (h : ∀ x∈xs,x.fits b) :
    (commonPair xs).fits ((b+1)*xs.length) := by
  induction xs with
  | nil => exact ⟨by simp [commonPair,Fits],Fits.one _⟩
  | cons x xs ih =>
    have A := h x List.mem_cons_self
    have B := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    have u : (b+1)*(xs.length+1)=b+(b+1)*xs.length+1 := by
      rw [Nat.mul_add,mul_one]
      omega
    change Fits ((b+1)*(xs.length+1)) (x.num*(commonPair xs).den+x.den*(commonPair xs).num) ∧
      Fits ((b+1)*(xs.length+1)) (x.den*(commonPair xs).den)
    rw [u]
    refine ⟨(A.1.mul B.2).add (A.2.mul B.1),?_⟩
    exact (A.2.mul B.2).mono (by simp)

def commonWordFee (p : ℕ) : ℕ := 4*(32*(p+1)^2)+16*p+20

def commonWord {p : ℕ} : List (FractionWord p) → Meter (FractionWord p)
  | [] => ⟨⟨wordZero p,wordOne p⟩,4*p+8⟩
  | x::xs =>
    let y := commonWord xs
    let a := mulWord x.num y.result.den
    let b := mulWord x.den y.result.num
    let c := mulWord x.den y.result.den
    let d := addWord a.result b.result
    ⟨⟨d.result,c.result⟩,y.steps+a.steps+b.steps+c.steps+d.steps+16*p+20⟩

theorem common_word_receipt {p : ℕ} (hp : 0<p)
    {xs : List (FractionWord p)} {ys : List Fraction}
    (h : List.Forall₂ FractionWord.matches xs ys) :
    (commonWord xs).result.matches (commonPair ys) ∧
    (commonWord xs).steps≤4*p+8+xs.length*commonWordFee p := by
  induction h with
  | nil =>
    constructor
    · change wordRead (wordZero p)=((0:ℤ):ZMod (2^p)) ∧ wordRead (wordOne p)=((1:ℤ):ZMod (2^p))
      simpa only [Int.cast_zero,Int.cast_one] using And.intro (wordOps p hp).zero_read (wordOne_read p hp)
    · simp [commonWord]
  | cons e h ih =>
    rename_i xa ya xas yas
    obtain ⟨v,t⟩ := ih
    change wordRead xa.num=(ya.num:ZMod (2^p)) ∧ wordRead xa.den=(ya.den:ZMod (2^p)) at e
    change wordRead (commonWord xas).result.num=((commonPair yas).num:ZMod (2^p)) ∧
      wordRead (commonWord xas).result.den=((commonPair yas).den:ZMod (2^p)) at v
    constructor
    · unfold FractionWord.matches
      simp only [commonWord,commonPair,addWord_read,mulWord_read,e.1,e.2,v.1,v.2,Int.cast_add,Int.cast_mul]
      trivial
    · let T := commonWord xas
      let A := mulWord xa.num T.result.den
      let B := mulWord xa.den T.result.num
      let C := mulWord xa.den T.result.den
      let D := addWord A.result B.result
      have u0 : A.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      have u1 : B.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      have u2 : C.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      have u3 : D.steps≤32*(p+1)^2 := (wordOps p hp).add_cost _ _
      change T.steps+A.steps+B.steps+C.steps+D.steps+16*p+20≤
        4*p+8+(xas.length+1)*commonWordFee p
      change T.steps≤_ at t
      rw [Nat.add_mul,one_mul]
      unfold commonWordFee at t ⊢
      omega

theorem word_lifts_int {p b : ℕ} (hp : 0<p) (z : Word p) (a : ℤ)
    (read : wordRead z=(a:ZMod (2^p))) (fit : Fits b a) (width : b+2≤p) :
    (centered hp z).result.value=a := by
  letI : NeZero (2^p:ℕ) := ⟨by positivity⟩
  rw [(centered_exact hp z).1]
  apply (ZMod.valMinAbs_spec _ _).mpr
  have h : (↑a.natAbs:ℤ)≤(↑((2:ℕ)^b):ℤ) := by exact_mod_cast fit
  rw [Int.natCast_natAbs] at h
  have hL : (2:ℕ)^b*4≤2^p := by
    rw [show 4=(2:ℕ)^2 by decide,←pow_add]
    exact Nat.pow_le_pow_right (by decide) width
  have hL' : (↑((2:ℕ)^b):ℤ)*4 ≤ (↑((2:ℕ)^p):ℤ) := by exact_mod_cast hL
  have P : (0:ℤ)<(↑((2:ℕ)^b):ℤ) := by positivity
  refine ⟨read,?_,?_⟩
  · change -(↑((2:ℕ)^p):ℤ)<a*2
    have e : -a≤(↑((2:ℕ)^b):ℤ) := (neg_le_abs a).trans h
    omega
  · change a*2≤(↑((2:ℕ)^p):ℤ)
    have e : a≤(↑((2:ℕ)^b):ℤ) := (le_abs_self a).trans h
    omega

def dropGuardWord {p : ℕ} (hp : 0<p) (q : FractionWord p) :
    Meter (Word p) :=
  let diff := subWord hp q.num q.den
  let A := centered hp diff.result
  let B := centered hp q.den
  let y := divideMagnitude A.result.magnitude B.result.magnitude
  ⟨y.result,diff.steps+A.steps+B.steps+y.steps+8⟩

def dropGuardFee (p : ℕ) := 32*(p+1)^2+70*p+28+signedDivisionFee p p

theorem abs_of_signed_value {p : ℕ} (x : SignedMagnitude p) :
    x.value.natAbs=bitsValue x.magnitude.val := by
  unfold SignedMagnitude.value signedDenote
  cases x.negative <;> simp

theorem drop_guard_word_exact {p b : ℕ} (hp : 0<p) (w : FractionWord p)
    (r : Fraction) (k : ℕ) (matchW : w.matches r) (nonzero : r.good)
    (value : r.value-1=(k:ℚ)) (fit : r.fits b) (capacity : b+3≤p) :
    bitsValue (dropGuardWord hp w).result.val=k ∧
    (dropGuardWord hp w).steps≤dropGuardFee p := by
  let diff := subWord hp w.num w.den
  let A := centered hp diff.result
  let B := centered hp w.den
  have d : wordRead diff.result=((r.num-r.den:ℤ):ZMod (2^p)) := by
    change wordRead (subWord hp w.num w.den).result=_
    rw [subWord_read,matchW.1,matchW.2,Int.cast_sub]
  have a0 : A.result.value=r.num-r.den :=
    word_lifts_int hp diff.result _ d (fit.1.sub fit.2) (by omega)
  have b0 : B.result.value=r.den :=
    word_lifts_int hp w.den _ matchW.2 fit.2 (by omega)
  have Bpos : 0<bitsValue B.result.magnitude.val := by
    rw [← abs_of_signed_value,b0]
    exact Int.natAbs_pos.mpr nonzero
  have dQ : (r.den:ℚ)≠0 := by exact_mod_cast nonzero
  have fac : r.num-r.den=r.den*(k:ℤ) := by
    apply Int.cast_injective (α:=ℚ)
    push_cast
    have H : (r.num:ℚ)/r.den=(k:ℚ)+1 := by unfold Fraction.value at value; linarith
    have K := (div_eq_iff dQ).mp H
    linarith
  have ta : bitsValue A.result.magnitude.val=bitsValue B.result.magnitude.val*k := by
    rw [← abs_of_signed_value A.result,← abs_of_signed_value B.result,a0,b0,fac,Int.natAbs_mul,Int.natAbs_natCast]
  have E := divide_magnitude_exact A.result.magnitude B.result.magnitude Bpos
  refine ⟨?_,?_⟩
  · change bitsValue (divideMagnitude A.result.magnitude B.result.magnitude).result.val=_
    rw [E.1,ta,mul_comm,Nat.mul_div_cancel k Bpos]
  · have cd : diff.steps≤32*(p+1)^2 := (wordOps p hp).sub_cost _ _
    have ca := (centered_exact hp diff.result).2
    have cb := (centered_exact hp w.den).2
    change A.steps≤35*p+10 at ca
    change B.steps≤35*p+10 at cb
    change diff.steps+A.steps+B.steps+(divideMagnitude A.result.magnitude B.result.magnitude).steps+8≤_
    rw [E.2]
    unfold dropGuardFee
    omega

def finishWords {p : ℕ} (hp : 0<p) (xs : List (FractionWord p)) : Meter (Word p) :=
  let x := commonWord xs
  let y := dropGuardWord hp x.result
  ⟨y.result,x.steps+y.steps+2⟩

theorem finish_words_exact {p b : ℕ} (hp : 0<p)
    (xs : List (FractionWord p)) (ys : List Fraction) (k : ℕ)
    (aligned : List.Forall₂ FractionWord.matches xs ys)
    (good : ∀ y∈ys,y.good) (small : ∀ y∈ys,y.fits b)
    (capacity : (b+1)*ys.length+3≤p) (correct : (clearRun ys).result.value-1=(k:ℚ)) :
    bitsValue (finishWords hp xs).result.val=k ∧
      (finishWords hp xs).steps≤4*p+10+xs.length*commonWordFee p+dropGuardFee p := by
  have H := common_word_receipt hp aligned
  have q := drop_guard_word_exact hp _ _ k H.1 (common_pair_good ys good)
    (by rwa [common_pair_value ys good]) (common_pair_fits ys b small) capacity
  refine ⟨q.1,?_⟩
  change (commonWord xs).steps+(dropGuardWord hp (commonWord xs).result).steps+2≤_
  omega

#print axioms common_pair_shape
#print axioms common_pair_good
#print axioms common_pair_value
#print axioms common_pair_fits
#print axioms common_word_receipt
#print axioms word_lifts_int
#print axioms abs_of_signed_value
#print axioms drop_guard_word_exact
#print axioms finish_words_exact
end J6R22RootReadout
