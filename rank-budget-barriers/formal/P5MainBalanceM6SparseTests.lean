import P5MainBalanceM6SparseCharts
import P5MainBalanceM6SparseEval
import Mathlib.Tactic.FinCases

/-! Exact monomial lists from the two printed sparse CNF reductions.
Neutral copies carry a separate owner and do not add to m_test. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical Polynomial

variable {V Copy I B : Type*} [LinearOrder B]
variable {G : Finset (V×V)} {left right : G→Fin 4}

/-- Base degree 2 on test rows and zero on neutral rows. -/
def testBase {F S : Type*} : (F⊕S)→ℕ
  | .inl _ => 2
  | .inr _ => 0

def isNeutral {F S : Type*} : (F⊕S)→Bool
  | .inl _ => false
  | .inr _ => true

private def uTerms (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) :
    (f : UFactor G)→Fin 4→List {p : UPort G // L.physical.factor p=f}
  | .inl (.inl v) => ![[],[L.pin v],[],[]]
  | .inl (.inr e) => ![[],[L.edge e false],[L.edge e true],[L.edge e false,L.edge e true]]
  | .inr _ => ![[],[],[],[]]

private def cTerms (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) :
    (f : CFactor G)→Fin 4→List {p : CPort G // L.physical.factor p=f}
  | .inl (.inl v) => ![[],[L.pin v],[],[]]
  | .inl (.inr (.inl e)) => ![[],[L.edge e false],[L.edge e true],[L.edge e false,L.edge e true]]
  | .inl (.inr (.inr (v,i))) => ![[],[L.cycle v i false],[],[L.cycle v i false,L.cycle v i true]]
  | .inr _ => ![[],[],[],[]]

private def uWeights (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) :
    (f : UFactor G)→({v : V // signedOwner L.physical (uMark G) v=f}→Bool)→Fin 4→ℚ
  | .inl (.inl v), s => ![if L.sign v s then 1 else 0,1,0,0]
  | .inl (.inr _), _ => ![1,1,1,1]
  | .inr _, _ => ![0,0,0,0]

private def cWeights (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) :
    (f : CFactor G)→({v : V // signedOwner L.physical (cMark G) v=f}→Bool)→Fin 4→ℚ
  | .inl (.inl v), s => ![if L.sign v s then 1 else 0,1,0,0]
  | .inl (.inr (.inl _)), _ => ![1,1,1,1]
  | .inl (.inr (.inr _)), _ => ![0,1,0,1]
  | .inr _, _ => ![0,0,0,0]

def uSource (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) : LiftSource L.physical (uMark G) where
  neutral := isNeutral
  number _ := 4
  terms := uTerms L
  weight := uWeights L
  small := by
    intro f k
    rcases f with (v|e)|v <;> fin_cases k <;> simp [uTerms]

def cSource (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) :
    LiftSource L.physical (cMark G) where
  neutral := isNeutral
  number _ := 4
  terms := cTerms L
  weight := cWeights L
  small := by
    intro f k
    rcases f with (v|e|⟨v,i⟩)|v <;> fin_cases k <;> simp [cTerms]

theorem uSource_base (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) :
    (uSource L).base=testBase := by
  funext f
  cases f <;> rfl

theorem cSource_base (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) :
    (cSource L).base=testBase := by
  funext f
  cases f <;> rfl

private theorem bit_cast (x : Bool) :
    (integerBit x:ℚ)=if x then 1 else 0 := by cases x <;> norm_num [integerBit]

set_option maxHeartbeats 9000000 in
theorem uSource_anchor_literal (L : UChart (Copy:=Copy) (I:=I) (B:=B) G)
    (f : UFactor G) (s : {v : V // signedOwner L.physical (uMark G) v=f}→Bool) (x : V→Bool)
    (y : ℤ) (h : uncloned_local G L.physical (uMark G) L.pin_owner f s x=some y) :
    (uSource L).anchorTest f s x=(y:ℚ) := by
  rcases f with (v|e)|v
  · change some (integerBit (x v)+integerBit (L.sign v s))=some y at h
    obtain rfl := Option.some.inj h
    simp [LiftSource.anchorTest,sumMonomials,uSource,uTerms,uWeights,letters,Fin.sum_univ_succ,
      UChart.pin,L.owner_is,uOwnerOf,qbits,BooleanMeasurement.bit,Int.cast_add,bit_cast]
    exact add_comm _ _
  · change some ((1+integerBit (x e.val.1))*(1+integerBit (x e.val.2)))=some y at h
    obtain rfl := Option.some.inj h
    cases hx : x e.val.1 <;> cases hy : x e.val.2 <;>
      simp [LiftSource.anchorTest,sumMonomials,uSource,uTerms,uWeights,letters,Fin.sum_univ_succ,
        UChart.edge,L.owner_is,uOwnerOf,qbits,BooleanMeasurement.bit,Int.cast_add,Int.cast_mul,bit_cast,hx,hy]
    norm_num
  · exact False.elim (Option.noConfusion h)

set_option maxHeartbeats 9000000 in
theorem cSource_anchor_literal (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right)
    (f : CFactor G) (s : {v : V // signedOwner L.physical (cMark G) v=f}→Bool)
    (x : V×Fin 4→Bool) (y : ℤ)
    (h : cloned_local G left right L.physical (cMark G) L.pin_owner f s x=some y) :
    (cSource L).anchorTest f s x=(y:ℚ) := by
  rcases f with (v|e|⟨v,i⟩)|v
  · change some (integerBit (x (v,0))+integerBit (L.sign v s))=some y at h
    obtain rfl := Option.some.inj h
    simp [LiftSource.anchorTest,sumMonomials,cSource,cTerms,cWeights,letters,Fin.sum_univ_succ,
      CChart.pin,L.owner_is,cOwnerOf,Direct.ownerOf,qbits,BooleanMeasurement.bit,Int.cast_add,bit_cast]
    exact add_comm _ _
  · change some ((1+integerBit (x (e.val.1,left e)))*(1+integerBit (x (e.val.2,right e))))=some y at h
    obtain rfl := Option.some.inj h
    cases hx : x (e.val.1,left e) <;> cases hy : x (e.val.2,right e) <;>
      simp [LiftSource.anchorTest,sumMonomials,cSource,cTerms,cWeights,letters,Fin.sum_univ_succ,
        CChart.edge,L.owner_is,cOwnerOf,Direct.ownerOf,qbits,BooleanMeasurement.bit,Int.cast_add,Int.cast_mul,bit_cast,hx,hy]
    norm_num
  · change some (integerBit (x (v,i))*(1+integerBit (x (v,i+1))))=some y at h
    obtain rfl := Option.some.inj h
    cases hx : x (v,i) <;> cases hy : x (v,i+1) <;>
      simp [LiftSource.anchorTest,sumMonomials,cSource,cTerms,cWeights,letters,Fin.sum_univ_succ,
        CChart.cycle,L.owner_is,cOwnerOf,Direct.ownerOf,qbits,BooleanMeasurement.bit,Int.cast_add,Int.cast_mul,bit_cast,hx,hy]
  · exact False.elim (Option.noConfusion h)

#print axioms uSource_base
#print axioms cSource_base
#print axioms uSource_anchor_literal
#print axioms cSource_anchor_literal
end P5MainBalance.M6.Sparse
