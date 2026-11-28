
import J6R22RootReadoutOuterWord

/-! Physical resident coordinate tape for the outer Lagrange row. The
program's pair slots are not supplied as an oracle: each is formed
from ordinary signed numerator/denominator coordinate words. Each
access to the sample tape is a paid sequential scan. -/
namespace J6R22RootReadout
open scoped BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates J9R19CompiledBits
set_option maxHeartbeats 12500000
set_option maxRecDepth 1200
set_option linter.unusedSectionVars false

structure CoordinateWord (p : ℕ) where
  n : Word p
  d : Word p
  sample : Word p

def CoordinateWord.realizes {p : ℕ} (a : CoordinateWord p) (n d s : ℤ) : Prop :=
  wordRead a.n=(n:ZMod (2^p)) ∧ wordRead a.d=(d:ZMod (2^p)) ∧ wordRead a.sample=(s:ZMod (2^p))

def coordFee (p : ℕ) := 8*p+12

def tapeCoord {p : ℕ} : ℕ → List (CoordinateWord p) → Meter (CoordinateWord p)
  | _, [] => ⟨⟨wordZero p,wordZero p,wordZero p⟩,coordFee p⟩
  | 0, c::_ => ⟨c,coordFee p⟩
  | j+1, _::cs =>
    let h := tapeCoord j cs
    ⟨h.result,h.steps+coordFee p⟩

theorem tape_coord_exact {p : ℕ} (xs : List (CoordinateWord p)) (i : ℕ) (hi : i<xs.length) :
    (tapeCoord i xs).result=xs[i] ∧ (tapeCoord i xs).steps≤(i+1)*coordFee p := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [tapeCoord]
    | succ i =>
      have hx : i<xs.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi
      obtain ⟨a,b⟩ := ih i hx
      constructor
      · simpa only [tapeCoord,List.getElem_cons_succ] using a
      · change (tapeCoord i xs).steps+coordFee p≤(i+1+1)*coordFee p
        rw [Nat.add_mul,one_mul]
        exact Nat.add_le_add_right b _

def lagWordFee (p : ℕ) := 5*(32*(p+1)^2)+18*p+22

def lagWord {p : ℕ} (hp : 0<p) (i j : CoordinateWord p) : Meter (FractionWord p) :=
  let x := subWord hp j.d j.n
  let n := mulWord x.result i.d
  let a := mulWord i.n j.d
  let b := mulWord j.n i.d
  let d := subWord hp a.result b.result
  ⟨⟨n.result,d.result⟩,x.steps+n.steps+a.steps+b.steps+d.steps+18*p+22⟩

theorem lag_word_exact {p : ℕ} (hp : 0<p) (a b : CoordinateWord p)
    (ni di si nj dj sj : ℤ) (x : a.realizes ni di si) (y : b.realizes nj dj sj) :
    (lagWord hp a b).result.matches (lagFactor ni di nj dj) ∧
    (lagWord hp a b).steps≤lagWordFee p := by
  constructor
  · unfold FractionWord.matches
    simp only [lagWord,lagFactor,subWord_read,mulWord_read,Int.cast_mul,Int.cast_sub,x.1,x.2.1,y.1,y.2.1]
    trivial
  · let v := subWord hp b.d b.n
    let n := mulWord v.result a.d
    let u := mulWord a.n b.d
    let w := mulWord b.n a.d
    let d := subWord hp u.result w.result
    have c0 : v.steps≤32*(p+1)^2 := (wordOps p hp).sub_cost _ _
    have c1 : n.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
    have c2 : u.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
    have c3 : w.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
    have c4 : d.steps≤32*(p+1)^2 := (wordOps p hp).sub_cost _ _
    change v.steps+n.steps+u.steps+w.steps+d.steps+18*p+22≤_
    unfold lagWordFee
    omega

def pairMulFee (p : ℕ) := 2*(32*(p+1)^2)+8*p+8

def pairMulWord {p : ℕ} (x y : FractionWord p) : Meter (FractionWord p) :=
  let n := mulWord x.num y.num
  let d := mulWord x.den y.den
  ⟨⟨n.result,d.result⟩,n.steps+d.steps+8*p+8⟩

theorem pair_mul_word_exact {p : ℕ} (hp : 0<p)
    (a b : FractionWord p) (x y : Fraction) (ha : a.matches x) (hb : b.matches y) :
    (pairMulWord a b).result.matches (x.times y) ∧ (pairMulWord a b).steps≤pairMulFee p := by
  constructor
  · unfold FractionWord.matches
    simp only [pairMulWord,mulWord_read,Fraction.times,Int.cast_mul,ha.1,ha.2,hb.1,hb.2]
    trivial
  · have h1 := (wordOps p hp).mul_cost a.num b.num
    have h2 := (wordOps p hp).mul_cost a.den b.den
    change (mulWord a.num b.num).steps≤32*(p+1)^2 at h1
    change (mulWord a.den b.den).steps≤32*(p+1)^2 at h2
    unfold pairMulFee
    change (mulWord a.num b.num).steps+(mulWord a.den b.den).steps+8*p+8≤_
    omega

def factorsWord {p : ℕ} {m : ℕ} (hp : 0<p)
    (xs : List (CoordinateWord p)) (i : CoordinateWord p) :
    List (Fin (m+1))→Meter (FractionWord p)
  | [] => ⟨⟨wordOne p,wordOne p⟩,6*p+8⟩
  | j::js =>
    let x := tapeCoord j.val xs
    let y := lagWord hp i x.result
    let z := factorsWord hp xs i js
    let prod := pairMulWord y.result z.result
    ⟨prod.result,x.steps+y.steps+z.steps+prod.steps+5⟩

def outerFactorFee (p m : ℕ) :=
  (m+1)*coordFee p+lagWordFee p+pairMulFee p+5

theorem factors_word_exact {p m : ℕ} (hp : 0<p)
    (xs : List (CoordinateWord p)) (len : xs.length=m+1)
    (I : CoordinateWord p) (ni di ai : ℤ)
    (hi : I.realizes ni di ai) (n d A : Fin (m+1)→ℤ)
    (chart : ∀ j : Fin (m+1), xs[j.val]'(by rw [len]; exact j.isLt) |>.realizes (n j) (d j) (A j))
    (js : List (Fin (m+1))) :
    (factorsWord hp xs I js).result.matches
      (fractionProduct (js.map fun j=>lagFactor ni di (n j) (d j))) ∧
    (factorsWord hp xs I js).steps≤6*p+8+js.length*outerFactorFee p m := by
  induction js with
  | nil =>
    constructor
    · change wordRead (wordOne p)=((1:ℤ):ZMod (2^p)) ∧ wordRead (wordOne p)=((1:ℤ):ZMod (2^p))
      simp only [wordOne_read p hp,Int.cast_one,and_self]
    · simp [factorsWord]
  | cons j js ih =>
    let x := tapeCoord j.val xs
    let y := lagWord hp I x.result
    let z := factorsWord hp xs I js
    let P := pairMulWord y.result z.result
    have hx := tape_coord_exact xs j.val (by rw [len]; exact j.isLt)
    have jx : x.result.realizes (n j) (d j) (A j) := by rw [show x.result=_ from hx.1]; exact chart j
    have hy := lag_word_exact hp I x.result ni di ai (n j) (d j) (A j) hi jx
    have out := pair_mul_word_exact hp y.result z.result _ _ hy.1 ih.1
    refine ⟨out.1,?_⟩
    have hxc : x.steps≤(j.val+1)*coordFee p := hx.2
    have loc : x.steps≤(m+1)*coordFee p := hxc.trans (Nat.mul_le_mul_right _ (by omega))
    have hys : y.steps≤lagWordFee p := hy.2
    have hz : z.steps≤6*p+8+js.length*outerFactorFee p m := ih.2
    have hout : P.steps≤pairMulFee p := out.2
    change x.steps+y.steps+z.steps+P.steps+5≤6*p+8+(js.length+1)*outerFactorFee p m
    rw [Nat.add_mul,one_mul]
    unfold outerFactorFee at hz ⊢
    omega

def termWord {p m : ℕ} (hp : 0<p) (xs : List (CoordinateWord p)) (i : Fin (m+1)) :
    Meter (FractionWord p) :=
  let x := tapeCoord i.val xs
  let dp := powerMod x.result.d (List.replicate m ())
  let L := factorsWord hp xs x.result (otherSites m i)
  let v := pairMulWord ⟨x.result.sample,dp.result⟩ L.result
  ⟨v.result,x.steps+dp.steps+L.steps+v.steps+16*(m+1)^2+10⟩

def outerTermFee (p m : ℕ) :=
  (m+1)*coordFee p+3*p+4+m*wordMulFee p+6*p+8+m*outerFactorFee p m+
    pairMulFee p+16*(m+1)^2+10

theorem term_word_exact {p m : ℕ} (hp : 0<p) (xs : List (CoordinateWord p))
    (len : xs.length=m+1) (n d A : Fin (m+1)→ℤ)
    (chart : ∀ j : Fin (m+1), xs[j.val]'(by rw [len]; exact j.isLt) |>.realizes (n j) (d j) (A j))
    (i : Fin (m+1)) :
    (termWord hp xs i).result.matches (termAtOne m n d A i) ∧
    (termWord hp xs i).steps≤outerTermFee p m := by
  let x := tapeCoord i.val xs
  let pw := powerMod x.result.d (List.replicate m ())
  let L := factorsWord hp xs x.result (otherSites m i)
  let V := pairMulWord ⟨x.result.sample,pw.result⟩ L.result
  have rc := tape_coord_exact xs i.val (by rw [len]; exact i.isLt)
  have xc : x.result.realizes (n i) (d i) (A i) := by rw [show x.result=_ from rc.1]; exact chart i
  have pd := power_mod_exact hp x.result.d (List.replicate m ())
  have sp : (FractionWord.mk x.result.sample pw.result).matches
      ⟨A i,(powerRun (d i) m).value⟩ := by
    refine ⟨xc.2.2,?_⟩
    change wordRead pw.result=_
    rw [show wordRead pw.result=_ from pd.1,List.length_replicate,xc.2.1,(powerRun_exact _ _).1,Int.cast_pow]
  have lc := factors_word_exact hp xs len x.result _ _ _ xc n d A chart (otherSites m i)
  have last := pair_mul_word_exact hp _ L.result _ _ sp lc.1
  refine ⟨last.1,?_⟩
  have cs : x.steps≤(m+1)*coordFee p := rc.2.trans (Nat.mul_le_mul_right _ (by omega))
  have ps := pd.2
  simp only [List.length_replicate] at ps
  have lcs := lc.2
  rw [other_sites_count] at lcs
  change x.steps+pw.steps+L.steps+V.steps+16*(m+1)^2+10≤_
  change pw.steps≤_ at ps
  change L.steps≤_ at lcs
  have res : V.steps≤pairMulFee p := last.2
  unfold outerTermFee
  omega

#print axioms tape_coord_exact
#print axioms lag_word_exact
#print axioms pair_mul_word_exact
#print axioms factors_word_exact
#print axioms term_word_exact
end J6R22RootReadout
