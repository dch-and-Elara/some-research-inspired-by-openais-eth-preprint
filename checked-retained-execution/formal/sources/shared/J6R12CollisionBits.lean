import J6R11CollisionCost
import AOracleMachineTimeTape

/-!
# Bit-serial arithmetic for one source packing score

A side endpoint consists only of its binary vertex identifier and an
optional binary word from the evolving label table. In two stages the
machine compares identifiers, then (if needed) assigned words. For
each side the numerator is 0, 1, or B, so the pair contributes one
of four fixed-width literals, without a multiplication instruction.
-/

namespace J6R12CollisionBits
open scoped BigOperators Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R11CollisionCost

def sameBits (x y : List Bool) : Meter Bool :=
  let s := orderCore (x.zip y)
  ⟨s.result.2,s.steps⟩

theorem sameBits_exact (x y : List Bool) (h : x.length=y.length) :
    ((sameBits x y).result=true ↔ bitsValue x=bitsValue y) ∧
    (sameBits x y).steps=10*x.length := by
  have ht := (orderCore_exact (x.zip y)).2
  simpa only [sameBits,zip_map_fst x y h,zip_map_snd x y h,List.length_zip,← h,min_self] using ht

inductive Digit
  | zero | one | full
  deriving DecidableEq

def Digit.val (B : ℕ) : Digit → ℕ
  | .zero => 0
  | .one => 1
  | .full => B

structure EndTape where
  addr : List Bool
  label : Option (List Bool)

def optionEqual (b : ℕ) (x y : Option (List Bool)) : Meter Digit :=
  match x,y with
  | some u,some v =>
    let q := sameBits u v
    ⟨if q.result then .full else .zero,q.steps+2*b+6⟩
  | _,_ => ⟨.one,6⟩

def sideTape (k b : ℕ) (x y : EndTape) : Meter Digit :=
  let q := sameBits x.addr y.addr
  if q.result then ⟨.full,q.steps+2*k+4⟩ else
    let v := optionEqual b x.label y.label
    ⟨v.result,q.steps+v.steps+2*k+4⟩

def packEnd {I A : Type*} (k b : ℕ) (addr : I → ℕ) (lab : A → ℕ)
    (p : I → Option A) (i : I) : EndTape :=
  ⟨encodeBits k (addr i),(p i).map (fun a => encodeBits b (lab a))⟩

section Side
variable {I A : Type*} [Fintype A]

theorem optionEqual_exact (b : ℕ) (lab : A → ℕ) (hl : Function.Injective lab)
    (hfit : ∀ a, lab a < 2^b) (u v : Option A) :
    let F := fun a => encodeBits b (lab a)
    let q := optionEqual b (u.map F) (v.map F)
    Digit.val (Fintype.card A) q.result =
      (match u,v with | some a,some c => if a=c then Fintype.card A else 0 | _,_ => 1) ∧
    q.steps ≤ 12*b+6 := by
  cases u with
  | none => cases v <;> simp [optionEqual,Digit.val]
  | some a =>
    cases v with
    | none => simp [optionEqual,Digit.val]
    | some c =>
      let Q := sameBits (encodeBits b (lab a)) (encodeBits b (lab c))
      have hQ := sameBits_exact (encodeBits b (lab a)) (encodeBits b (lab c))
        (by simp [encodeBits_length])
      have hq : Q.result=true ↔ a=c := by
        rw [hQ.1, encodeBits_exact _ _ (hfit a),encodeBits_exact _ _ (hfit c),hl.eq_iff]
      have hs : Q.steps=10*b := hQ.2.trans (by rw [encodeBits_length])
      change Digit.val (Fintype.card A) (if Q.result then .full else .zero) = _ ∧
        Q.steps+2*b+6≤12*b+6
      by_cases h : a=c
      · simp [h,hq.mpr h,hs,Digit.val]; omega
      · have hh : ¬Q.result=true := hq.not.mpr h
        simp [h,hh,hs,Digit.val]; omega

/-- The endpoint comparison depends on its vertex identifier, not merely
the assigned contents of its slot. Both assigned labels are compared
only when the vertices differ. -/
theorem sideTape_exact (k b : ℕ) (addr : I → ℕ) (lab : A → ℕ)
    (hAddr : Function.Injective addr) (hLab : Function.Injective lab)
    (hA : ∀ i, addr i < 2^k) (hL : ∀ a, lab a < 2^b)
    (p : I → Option A) (i j : I) :
    let q := sideTape k b (packEnd k b addr lab p i) (packEnd k b addr lab p j)
    Digit.val (Fintype.card A) q.result = side p i j ∧
    q.steps ≤ 12*k+12*b+10 := by
  let x := packEnd k b addr lab p i
  let y := packEnd k b addr lab p j
  let Q := sameBits x.addr y.addr
  have hQ := sameBits_exact x.addr y.addr (by simp [x,y,packEnd,encodeBits_length])
  have hb : Q.result=true ↔ i=j := by
    rw [hQ.1]
    simp only [x,y,packEnd,encodeBits_exact _ _ (hA _),hAddr.eq_iff]
  have hs : Q.steps=10*k := hQ.2.trans (by simp [x,packEnd,encodeBits_length])
  change Digit.val _ (sideTape k b x y).result=side p i j ∧ _
  by_cases hij : i=j
  · have hh : (sameBits x.addr y.addr).result=true := hb.mpr hij
    rw [sideTape,if_pos hh,side,if_pos hij]
    change Digit.val _ .full=_ ∧ Q.steps+2*k+4≤_
    exact ⟨rfl,by omega⟩
  · have hh : ¬(sameBits x.addr y.addr).result=true := hb.not.mpr hij
    have ho := optionEqual_exact b lab hLab hL (p i) (p j)
    rw [sideTape,if_neg hh,side,if_neg hij]
    change Digit.val _ (optionEqual b x.label y.label).result = _ ∧
      Q.steps+(optionEqual b x.label y.label).steps+2*k+4≤_
    refine ⟨ho.1,?_⟩
    have hv : (optionEqual b x.label y.label).steps≤12*b+6 := ho.2
    omega

end Side

structure PairTape where
  r₁ : EndTape
  r₂ : EndTape
  c₁ : EndTape
  c₂ : EndTape

structure Literals where
  zero : List Bool
  one : List Bool
  full : List Bool
  square : List Bool

def makeLiterals (w B : ℕ) : Literals :=
  ⟨encodeBits w 0,encodeBits w 1,encodeBits w B,encodeBits w (B^2)⟩

def termBits (L : Literals) : Digit → Digit → List Bool
  | .zero,_ => L.zero
  | _,.zero => L.zero
  | .one,.one => L.one
  | .full,.full => L.square
  | _,_ => L.full

theorem termBits_exact (w B : ℕ) (h₁ : 1 < 2^w) (hB : B < 2^w) (hBB : B^2 < 2^w)
    (x y : Digit) :
    let t := termBits (makeLiterals w B) x y
    t.length=w ∧ bitsValue t=Digit.val B x*Digit.val B y := by
  have h₀ : 0 < 2^w := by positivity
  have h₂ : B*B < 2^w := by simpa only [pow_two] using hBB
  cases x <;> cases y <;>
    simp [makeLiterals,termBits,Digit.val,encodeBits_length,encodeBits_exact _ _ h₀,
      encodeBits_exact _ _ h₁,encodeBits_exact _ _ hB,encodeBits_exact _ _ h₂,pow_two]

def pairBits (kR kC b w : ℕ) (L : Literals) (p : PairTape) : Meter (List Bool) :=
  let r := sideTape kR b p.r₁ p.r₂
  let c := sideTape kC b p.c₁ p.c₂
  ⟨termBits L r.result c.result,r.steps+c.steps+2*w+8⟩

/-- Receiver layout: charge two side comparisons, reading the selected
w-bit constant, and copying it to the term register. -/
def pairBudget (kR kC b w : ℕ) : ℕ := 12*kR+12*kC+24*b+2*w+28

def packPair {E R C A : Type*} (kR kC b : ℕ)
    (rCode : R → ℕ) (cCode : C → ℕ) (aCode : A → ℕ)
    (row : E → R) (col : E → C) (p : R⊕C → Option A) (ef : E×E) : PairTape :=
  ⟨packEnd kR b rCode aCode (fun i => p (.inl i)) (row ef.1),
   packEnd kR b rCode aCode (fun i => p (.inl i)) (row ef.2),
   packEnd kC b cCode aCode (fun i => p (.inr i)) (col ef.1),
   packEnd kC b cCode aCode (fun i => p (.inr i)) (col ef.2)⟩

theorem packed_pair_exact {E R C A : Type*} [Fintype A] (kR kC b w : ℕ)
    (rCode : R → ℕ) (cCode : C → ℕ) (aCode : A → ℕ)
    (hr : Function.Injective rCode) (hc : Function.Injective cCode) (ha : Function.Injective aCode)
    (hR : ∀ i, rCode i<2^kR) (hC : ∀ i, cCode i<2^kC) (hA : ∀ i, aCode i<2^b)
    (h₁ : 1<2^w) (hB : Fintype.card A<2^w) (hBB : (Fintype.card A)^2<2^w)
    (row : E → R) (col : E → C) (p : R⊕C → Option A) (ef : E×E) :
    let q := pairBits kR kC b w (makeLiterals w (Fintype.card A))
      (packPair kR kC b rCode cCode aCode row col p ef)
    q.result.length=w ∧ bitsValue q.result=contribution row col p ef ∧
    q.steps≤pairBudget kR kC b w := by
  let t := packPair kR kC b rCode cCode aCode row col p ef
  let u := sideTape kR b t.r₁ t.r₂
  let v := sideTape kC b t.c₁ t.c₂
  have H := termBits_exact w (Fintype.card A) h₁ hB hBB u.result v.result
  obtain ⟨hur,hus⟩ := sideTape_exact kR b rCode aCode hr ha hR hA
    (fun i => p (.inl i)) (row ef.1) (row ef.2)
  obtain ⟨hvr,hvs⟩ := sideTape_exact kC b cCode aCode hc ha hC hA
    (fun i => p (.inr i)) (col ef.1) (col ef.2)
  change Digit.val _ u.result = _ at hur
  change Digit.val _ v.result = _ at hvr
  change u.steps≤_ at hus
  change v.steps≤_ at hvs
  refine ⟨H.1,?_ ,?_⟩
  · change bitsValue (termBits _ u.result v.result) = _
    rw [H.2,hur,hvr]
    simp [contribution,side]
  · change u.steps+v.steps+2*w+8≤pairBudget _ _ _ _
    unfold pairBudget
    omega

#print axioms sameBits_exact
#print axioms optionEqual_exact
#print axioms sideTape_exact
#print axioms termBits_exact
#print axioms packed_pair_exact

end J6R12CollisionBits
