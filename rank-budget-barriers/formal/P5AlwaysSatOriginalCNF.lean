import PinnedCNF
import GraphCutMoments
import Mathlib.Tactic

/-! Pro v7 §4.5 (M.7): the one global y switch and the separate b0 and
per-vertex bonus switches of the original CNF. No edge-switch substitute. -/
namespace Paper5.AlwaysSatOriginal
open scoped BigOperators

abbrev Var {V : Type*} (T : Finset V) := V ⊕ (Bool ⊕ ↥T)
abbrev Factor {V : Type*} (E : Finset (V×V)) (T : Finset V) :=
  V ⊕ (↥E ⊕ (Unit ⊕ (↥T×Bool)))

variable {V : Type*} {T : Finset V}

def old (v : V) : Var T := .inl v
def y (T : Finset V) : Var T := .inr (.inl false)
def b₀ (T : Finset V) : Var T := .inr (.inl true)
def bonus (v : ↥T) : Var T := .inr (.inr v)

def clause (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Factor E T→Std.Sat.CNF.Clause (Var T)
  | .inl v => [(old v,s v)]
  | .inr (.inl e) => [(y T,false),(old e.val.1,true),(old e.val.2,true)]
  | .inr (.inr (.inl _)) => [(b₀ T,false),(y T,false)]
  | .inr (.inr (.inr (v,false))) => [(bonus v,false),(old v.val,true)]
  | .inr (.inr (.inr (v,true))) => [(bonus v,false),(y T,false)]

noncomputable def formula [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Std.Sat.CNF (Var T) :=
  (Finset.univ : Finset (Factor E T)).toList.map (clause E T s)

def assignment (T : Finset V) (s : V→Bool) (Y B : Bool) (G : ↥T→Bool) : Var T→Bool
  | .inl v => s v
  | .inr (.inl false) => Y
  | .inr (.inl true) => B
  | .inr (.inr v) => G v

@[simp] theorem assignment_old (T : Finset V) (s : V→Bool) (Y B : Bool) (G : ↥T→Bool) (v : V) :
    assignment T s Y B G (old v)=s v := rfl
@[simp] theorem assignment_y (T : Finset V) (s : V→Bool) (Y B : Bool) (G : ↥T→Bool) :
    assignment T s Y B G (y T)=Y := rfl
@[simp] theorem assignment_b₀ (T : Finset V) (s : V→Bool) (Y B : Bool) (G : ↥T→Bool) :
    assignment T s Y B G (b₀ T)=B := rfl
@[simp] theorem assignment_bonus (T : Finset V) (s : V→Bool) (Y B : Bool) (G : ↥T→Bool) (v : ↥T) :
    assignment T s Y B G (bonus v)=G v := rfl

theorem cnf_sat_all_clauses [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool)
    (a : Var T→Bool) :
    (formula E T s).Sat a ↔ ∀ i : Factor E T,(clause E T s i).eval a=true := by
  simp [Std.Sat.CNF.sat_def,formula,Std.Sat.CNF.eval,List.all_eq_true]

def fixedPins (T : Finset V) (s : V→Bool) (a : Var T→Bool) : Prop :=
  ∀ v : V,a (old v)=s v

def bonusAllowed (T : Finset V) (s : V→Bool) (a : Var T→Bool) : Prop :=
  ∀ v : ↥T,a (bonus v)=true → s v.val=true

def allBonusesZero (T : Finset V) (a : Var T→Bool) : Prop :=
  a (b₀ T)=false ∧ ∀ v : ↥T,a (bonus v)=false

/-- The branch conditions are exactly those of the literal displayed clauses. -/
theorem sat_iff_branches [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool)
    (a : Var T→Bool) :
    (formula E T s).Sat a ↔ fixedPins T s a ∧
      (if a (y T) then PinnedCNF.AllEdges E s ∧ allBonusesZero T a else bonusAllowed T s a) := by
  rw [cnf_sat_all_clauses]
  constructor
  · intro h
    have hp : ∀ v : V,a (old (T:=T) v)=s v := fun v=>by simpa [clause] using h (.inl v)
    refine ⟨hp,?_⟩
    cases hy : a (y T) with
    | false =>
      simp only [Bool.false_eq_true,if_false]
      intro t ht
      simpa [clause,hp,ht] using h (.inr (.inr (.inr (t,false))))
    | true =>
      simp only [if_true]
      refine ⟨?_,?_,?_⟩
      · intro e he
        simpa [clause,hy,hp] using h (.inr (.inl ⟨e,he⟩))
      · simpa [clause,hy] using h (.inr (.inr (.inl ())))
      · intro t
        simpa [clause,hy] using h (.inr (.inr (.inr (t,true))))
  · rintro ⟨hp,hh⟩ i
    change ∀ v : V,a (old (T:=T) v)=s v at hp
    have permitted : bonusAllowed T s a := by
      intro t ht
      cases hy : a (y T) with
      | false => exact (show bonusAllowed T s a from by simpa [hy] using hh) t ht
      | true =>
        have hj : PinnedCNF.AllEdges E s ∧ allBonusesZero T a := by simpa [hy] using hh
        exact (Bool.false_ne_true ((hj.2.2 t).symm.trans ht)).elim
    rcases i with v|(e|(_|⟨t,b⟩))
    · simpa [clause] using hp v
    · cases hy : a (y T) with
      | false => simp [clause,hy]
      | true =>
        have hj : PinnedCNF.AllEdges E s ∧ allBonusesZero T a := by simpa [hy] using hh
        simpa [clause,hy,hp] using hj.1 e.val e.property
    · cases hy : a (y T) with
      | false => simp [clause,hy]
      | true =>
        have hj : PinnedCNF.AllEdges E s ∧ allBonusesZero T a := by simpa [hy] using hh
        simp [clause,hy,hj.2.1]
    · cases b with
      | false =>
        cases hb : a (bonus t) with
        | false => simp [clause,hb]
        | true => simp [clause,hb,hp,permitted t hb]
      | true =>
        cases hy : a (y T) with
        | false => simp [clause,hy]
        | true =>
          have hj : PinnedCNF.AllEdges E s ∧ allBonusesZero T a := by simpa [hy] using hh
          simp [clause,hy,hj.2.2 t]

theorem all_signs_sat [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    (formula E T s).Sat (assignment T s false false (fun _=>false)) := by
  rw [sat_iff_branches]
  simp [fixedPins,bonusAllowed]

theorem factor_card [Fintype V] (E : Finset (V×V)) (T : Finset V) :
    Fintype.card (Factor E T)=Fintype.card V+E.card+2*T.card+1 := by
  simp [Factor,Nat.two_mul,Nat.mul_two]
  omega

theorem formula_length [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    (formula E T s).length=Fintype.card V+E.card+2*T.card+1 := by
  simpa [formula] using factor_card E T

theorem literal_occurrences [Fintype V] (E : Finset (V×V)) (T : Finset V)
    (s : V→Bool) :
    (∑ i : Factor E T,(clause E T s i).length)=Fintype.card V+3*E.card+4*T.card+2 := by
  simp [Factor,Fintype.sum_sum_type,Fintype.sum_prod_type,clause,Nat.mul_comm]
  omega

theorem cubic_original_sizes [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (T : Finset V) (s : V→Bool)
    (hC : ∀ v,GraphCutMoments.degree E v=3) :
    2*(formula E T s).length=5*Fintype.card V+4*T.card+2 ∧
    2*(∑ i : Factor E T,(clause E T s i).length)=11*Fintype.card V+8*T.card+4 := by
  rw [formula_length,literal_occurrences]
  have he := GraphCutMoments.regular_edge_count E 3 hC
  omega

#print axioms cnf_sat_all_clauses
#print axioms sat_iff_branches
#print axioms all_signs_sat
#print axioms factor_card
#print axioms formula_length
#print axioms literal_occurrences
#print axioms cubic_original_sizes
end Paper5.AlwaysSatOriginal