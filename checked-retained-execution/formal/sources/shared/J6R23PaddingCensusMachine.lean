
import J6R22RootReadoutOddRoot
import J6R23PaddingCensusGeometry

/-! The branch-free source match is computed by two serial comparisons
and one word addition; census counts use a saturated two-bit state.
The proof uses the extra ordinal bit to rule out modular wrap. -/
namespace J6R23PaddingCensus
open scoped BigOperators
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open J6R22RootReadout
set_option maxHeartbeats 14500000
set_option linter.unusedSectionVars false

structure SeatWord (K W : ℕ) where
  page : Word K
  ordinal : Word W

def SeatWord.represents {K W L : ℕ} {P : Type*} (r : SeatWord K W)
    (code : P→ℕ) (seat : P×Fin L) : Prop :=
  bitsValue r.page.val=code seat.1 ∧ bitsValue r.ordinal.val=seat.2.val

structure PadColumnWord (K W : ℕ) where
  neg : SeatWord K W
  pos : SeatWord K W

def PadColumnWord.represents {K W L : ℕ} {P : Type*} (r : PadColumnWord K W)
    (code : P→ℕ) (f : Bool→(P×Fin L)) : Prop :=
  r.neg.represents code (f false) ∧ r.pos.represents code (f true)

def shiftFee (K W : ℕ) := 10*K+10*W+32*(W+1)^2+8*(K+W+1)

def shiftWord {K W : ℕ} (delta : Word W) (A B : SeatWord K W) : Meter Bool :=
  let same := A1R9.eqWord A.page.val B.page.val
  let s := addWord A.ordinal delta
  let hit := A1R9.eqWord s.result.val B.ordinal.val
  ⟨same.result && hit.result,same.steps+s.steps+hit.steps+8*(K+W+1)⟩

theorem shift_word_exact {K W L : ℕ} {P : Type*}
    (hp : 0<W) (delta : Word W) (t : ℕ) (ht : bitsValue delta.val=t) (hL : t<L)
    (width : 2*L≤2^W) (code : P→ℕ) (inj : Function.Injective code)
    (x y : P×Fin L) (A B : SeatWord K W)
    (a : A.represents code x) (b : B.represents code y) :
    ((shiftWord delta A B).result=true ↔ sameShift t x y) ∧
    (shiftWord delta A B).steps≤shiftFee K W := by
  let same := A1R9.eqWord A.page.val B.page.val
  let S := addWord A.ordinal delta
  let hit := A1R9.eqWord S.result.val B.ordinal.val
  obtain ⟨peq,pc⟩ := A1R9.eqWord_exact A.page.val B.page.val (A.page.property.trans B.page.property.symm)
  obtain ⟨sub,hc⟩ := A1R9.eqWord_exact S.result.val B.ordinal.val (S.result.property.trans B.ordinal.property.symm)
  have V : bitsValue S.result.val = x.2.val+t := by
    have ac : bitsValue A.ordinal.val+bitsValue delta.val<2^W := by
      rw [a.2,ht]
      have e := x.2.isLt
      omega
    rw [show bitsValue S.result.val=_ from add_nat_word A.ordinal delta ac,a.2,ht]
  have pe : same.result=true ↔ x.1=y.1 := by
    change (A1R9.eqWord A.page.val B.page.val).result=true ↔ _
    rw [peq,a.1,b.1]
    exact inj.eq_iff
  have he : hit.result=true ↔ x.2.val+t=y.2.val := by
    change (A1R9.eqWord S.result.val B.ordinal.val).result=true ↔ _
    rw [sub,V,b.2]
  constructor
  · change (same.result&&hit.result)=true ↔ _
    rw [Bool.and_eq_true,pe,he]
    rfl
  · have sc : S.steps≤32*(W+1)^2 := (wordOps W hp).add_cost _ _
    change same.steps=10*A.page.val.length at pc
    change hit.steps=10*S.result.val.length at hc
    change same.steps+S.steps+hit.steps+8*(K+W+1)≤_
    rw [A.page.property] at pc
    rw [S.result.property] at hc
    unfold shiftFee
    omega

def hitFee (K W : ℕ) := 2*shiftFee K W+12*(K+W+1)+8

def hitWord {K W : ℕ} (delta : Word W) (src dst : PadColumnWord K W) : Meter Bool :=
  let low := shiftWord delta src.neg dst.neg
  let high := shiftWord delta src.neg dst.pos
  ⟨low.result||high.result,low.steps+high.steps+12*(K+W+1)+8⟩

theorem hit_word_exact {K W L : ℕ} {P : Type*}
    (hp : 0<W) (delta : Word W) (t : ℕ) (ht : bitsValue delta.val=t) (hL : t<L)
    (width : 2*L≤2^W) (code : P→ℕ) (inj : Function.Injective code)
    (x y : Bool→P×Fin L) (A B : PadColumnWord K W)
    (a : A.represents code x) (b : B.represents code y) :
    ((hitWord delta A B).result=true ↔ sameShift t (x false) (y false) ∨ sameShift t (x false) (y true)) ∧
    (hitWord delta A B).steps≤hitFee K W := by
  obtain ⟨L,C⟩ := shift_word_exact hp delta t ht hL width code inj _ _ A.neg B.neg a.1 b.1
  obtain ⟨R,D⟩ := shift_word_exact hp delta t ht hL width code inj _ _ A.neg B.pos a.1 b.2
  refine ⟨?_,?_⟩
  · change ((shiftWord delta A.neg B.neg).result||(shiftWord delta A.neg B.pos).result)=true ↔ _
    rw [Bool.or_eq_true,L,R]
  · change (shiftWord delta A.neg B.neg).steps+(shiftWord delta A.neg B.pos).steps+12*(K+W+1)+8≤_
    unfold hitFee
    omega

theorem hit_word_cost {K W : ℕ} (hp : 0<W) (delta : Word W) (A B : PadColumnWord K W) :
    (hitWord delta A B).steps≤hitFee K W := by
  have h (r s : SeatWord K W) : (shiftWord delta r s).steps≤shiftFee K W := by
    let E := A1R9.eqWord r.page.val s.page.val
    let a := addWord r.ordinal delta
    let M := A1R9.eqWord a.result.val s.ordinal.val
    have e1 := (A1R9.eqWord_exact r.page.val s.page.val (r.page.property.trans s.page.property.symm)).2
    have e2 := (A1R9.eqWord_exact a.result.val s.ordinal.val (a.result.property.trans s.ordinal.property.symm)).2
    have c : a.steps≤32*(W+1)^2 := (wordOps W hp).add_cost _ _
    change E.steps=10*r.page.val.length at e1
    change M.steps=10*a.result.val.length at e2
    rw [r.page.property] at e1
    rw [a.result.property] at e2
    change E.steps+a.steps+M.steps+8*(K+W+1)≤_
    unfold shiftFee
    omega
  have l := h A.neg B.neg
  have r := h A.neg B.pos
  change (shiftWord delta A.neg B.neg).steps+(shiftWord delta A.neg B.pos).steps+12*(K+W+1)+8≤_
  unfold hitFee
  omega

def saturated (n : ℕ) : Fin 3 := ⟨min 2 n,by omega⟩

def countHits {K W : ℕ} (delta : Word W) (q : PadColumnWord K W) :
    List (PadColumnWord K W)→Meter (Fin 3)
  | [] => ⟨0,5⟩
  | p::ps =>
    let z := hitWord delta p q
    let tail := countHits delta q ps
    ⟨if z.result then saturated (tail.result.val+1) else tail.result,
      z.steps+tail.steps+12⟩

def tallyFee (K W : ℕ) := hitFee K W+12

theorem count_hits_exact {K W : ℕ} (hp : 0<W)
    (delta : Word W) (q : PadColumnWord K W) (src : List (PadColumnWord K W)) :
    (countHits delta q src).result.val=min 2 (src.countP (fun p=>(hitWord delta p q).result)) ∧
    (countHits delta q src).steps≤5+src.length*tallyFee K W := by
  induction src with
  | nil => simp [countHits]
  | cons x xs ih =>
    let b := hitWord delta x q
    let rest := countHits delta q xs
    have h := hit_word_cost hp delta x q
    refine ⟨?_,?_⟩
    · change (if b.result then saturated (rest.result.val+1) else rest.result).val=min 2 _
      rw [List.countP_cons]
      change (if b.result then saturated (rest.result.val+1) else rest.result).val =
        min 2 (xs.countP (fun p=>(hitWord delta p q).result)+(if b.result then 1 else 0))
      have recVal : rest.result.val=min 2 (xs.countP (fun p=>(hitWord delta p q).result)) := ih.1
      cases b.result <;> simp only [Bool.false_eq_true,if_false,if_true,saturated,recVal]
      all_goals omega
    · have hc : rest.steps≤5+xs.length*tallyFee K W := ih.2
      have bc : b.steps≤hitFee K W := h
      change b.steps+rest.steps+12≤5+(xs.length+1)*tallyFee K W
      rw [Nat.add_mul,one_mul]
      unfold tallyFee at hc ⊢
      omega

def censusSweep {K W : ℕ} (delta : Word W) (src : List (PadColumnWord K W)) :
    List (PadColumnWord K W)→Meter (List (Fin 3))
  | [] => ⟨[],5⟩
  | c::cs =>
    let z := countHits delta c src
    let tail := censusSweep delta src cs
    ⟨z.result::tail.result,z.steps+tail.steps+10⟩

theorem census_sweep_receipt {K W : ℕ} (hp : 0<W) (delta : Word W)
    (src dst : List (PadColumnWord K W)) :
    (censusSweep delta src dst).result=dst.map (fun d=>(countHits delta d src).result) ∧
    (censusSweep delta src dst).steps≤5+dst.length*(15+src.length*tallyFee K W) := by
  induction dst with
  | nil => simp [censusSweep]
  | cons c cs ih =>
    have k := (count_hits_exact hp delta c src).2
    constructor
    · simp only [censusSweep,List.map_cons,ih.1]
    · change (countHits delta c src).steps+(censusSweep delta src cs).steps+10≤
        5+(cs.length+1)*(15+src.length*tallyFee K W)
      rw [Nat.add_mul,one_mul]
      have t := ih.2
      omega

def censusWords {K W : ℕ} (delta : Word W) (layout : List (PadColumnWord K W)) :
    Meter (List (Fin 3)) :=
  censusSweep delta layout layout

#print axioms shift_word_exact
#print axioms hit_word_exact
#print axioms hit_word_cost
#print axioms count_hits_exact
#print axioms census_sweep_receipt
end J6R23PaddingCensus
