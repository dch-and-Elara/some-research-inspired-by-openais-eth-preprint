import Init

/-! The finite conflict-graph core of v8 F5. Vertices are literal occurrence
slots, not variables. Edge/triple requests are attached to clause cliques.
This file does not supply the physical F1 compiler or the ambient graph. -/

namespace F5R59
set_option autoImplicit false

structure Literal (V : Type) where
  var : V
  positive : Bool

structure ClauseSystem (C V : Type) where
  width : C → Nat
  literal : (c : C) → Fin (width c) → Literal V

variable {C V : Type}

abbrev Vertex (S : ClauseSystem C V) := Sigma (fun c : C => Fin (S.width c))

def term (S : ClauseSystem C V) (x : Vertex S) : Literal V := S.literal x.1 x.2

def opposite (S : ClauseSystem C V) (x y : Vertex S) : Prop :=
  (term S x).var = (term S y).var ∧ (term S x).positive ≠ (term S y).positive

def conflict (S : ClauseSystem C V) (x y : Vertex S) : Prop :=
  x ≠ y ∧ (x.1 = y.1 ∨ opposite S x y)

def satisfies (S : ClauseSystem C V) (a : V → Bool) : Prop :=
  ∀ c, ∃ i : Fin (S.width c), a (S.literal c i).var = (S.literal c i).positive

def isIndependent (S : ClauseSystem C V) (I : Vertex S → Prop) : Prop :=
  ∀ x y, I x → I y → ¬ conflict S x y

def meetsClauses (S : ClauseSystem C V) (I : Vertex S → Prop) : Prop :=
  ∀ c, ∃ i : Fin (S.width c), I ⟨c,i⟩

theorem graph_symmetric (S : ClauseSystem C V) {x y : Vertex S} (h : conflict S x y) :
    conflict S y x := by
  refine ⟨Ne.symm h.1, ?_⟩
  cases h.2 with
  | inl e => exact Or.inl e.symm
  | inr e => exact Or.inr ⟨e.1.symm, Ne.symm e.2⟩

theorem graph_irreflexive (S : ClauseSystem C V) (x : Vertex S) : ¬ conflict S x x :=
  fun h => h.1 rfl

theorem meets_clause_exactly_one (S : ClauseSystem C V) (I : Vertex S → Prop)
    (hi : isIndependent S I) (hm : meetsClauses S I) (c : C) :
    ∃ i : Fin (S.width c), I ⟨c,i⟩ ∧ ∀ j : Fin (S.width c), I ⟨c,j⟩ → j = i := by
  obtain ⟨i,h⟩ := hm c
  refine ⟨i,h,?_⟩
  intro j hj
  by_cases e : j = i
  · exact e
  · exfalso
    apply hi ⟨c,j⟩ ⟨c,i⟩ hj h
    refine ⟨?_, Or.inl rfl⟩
    intro bad
    cases bad
    exact e rfl

theorem decision_equivalence (S : ClauseSystem C V) :
    (∃ a, satisfies S a) ↔ ∃ I, isIndependent S I ∧ meetsClauses S I := by
  classical
  constructor
  · rintro ⟨a,h⟩
    let pick : (c : C) → Fin (S.width c) := fun c => Classical.choose (h c)
    have truePick (c : C) : a (S.literal c (pick c)).var = (S.literal c (pick c)).positive :=
      Classical.choose_spec (h c)
    let I : Vertex S → Prop := fun x => x.2 = pick x.1
    refine ⟨I,?_,fun c => ⟨pick c,rfl⟩⟩
    rintro ⟨c,i⟩ ⟨d,j⟩ hi hj ⟨hn,hr⟩
    change i = pick c at hi
    change j = pick d at hj
    subst i
    subst j
    rcases hr with eq | ⟨sameVar,differentSign⟩
    · cases eq
      exact hn rfl
    · apply differentSign
      change (S.literal c (pick c)).var = (S.literal d (pick d)).var at sameVar
      change (S.literal c (pick c)).positive = (S.literal d (pick d)).positive
      exact (truePick c).symm.trans ((congrArg a sameVar).trans (truePick d))
  · rintro ⟨I,hi,hm⟩
    let a : V → Bool := fun v =>
      if ∃ y, I y ∧ (term S y).var = v ∧ (term S y).positive = true then true else false
    refine ⟨a,fun c => ?_⟩
    obtain ⟨i,hx⟩ := hm c
    let x : Vertex S := ⟨c,i⟩
    refine ⟨i, ?_⟩
    change a (term S x).var = (term S x).positive
    cases h : (term S x).positive with
    | true =>
      exact if_pos ⟨x,hx,rfl,h⟩
    | false =>
      apply if_neg
      rintro ⟨y,hy,eq,ht⟩
      have diff : (term S x).positive ≠ (term S y).positive := by
        rw [h,ht]
        decide
      have ne : x ≠ y := fun e => diff (congrArg (fun z => (term S z).positive) e)
      exact hi x y hx hy ⟨ne, Or.inr ⟨eq.symm,diff⟩⟩

#print axioms graph_symmetric
#print axioms graph_irreflexive
#print axioms meets_clause_exactly_one
#print axioms decision_equivalence

end F5R59

