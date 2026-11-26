import P5HybridClosureDPack

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

/-! A full-word distribution with a different tie rule at each coordinate.
The coordinate remains part of every primitive key, even after tying:
one exterior pair and one triangle never share a primitive in two
different coordinates. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance

section Key

variable {A B T I S E : Type*}

abbrev Atom (A B T I : Type*) := ((A ⊕ T) ⊕ B) × I

def tiedAtom (tag : I→A→Option T) (a : A) (i : I) : Atom A B T I :=
  (.inl ((tag i a).elim (.inl a) Sum.inr),i)

def freeAtom (b : B) (i : I) : Atom A B T I := (.inr b,i)

def rowWord (tag : I→A→Option T) (cfg : Atom A B T I→S) (a : A) : I→S :=
  fun i=>cfg (tiedAtom tag a i)

def colWord (cfg : Atom A B T I→S) (b : B) : I→S :=
  fun i=>cfg (freeAtom b i)

def orderedCell (tag : I→A→Option T) (ar : E→A) (bc : E→B)
    (cfg : Atom A B T I→S) (e : E) : Draw I S :=
  (rowWord tag cfg (ar e),colWord cfg (bc e))

theorem same_tag_same_symbol (tag : I→A→Option T) (cfg : Atom A B T I→S)
    {i : I} {a a' : A} {t : T} (h : tag i a=some t) (h' : tag i a'=some t) :
    rowWord tag cfg a i=rowWord tag cfg a' i := by
  simp [rowWord,tiedAtom,h,h']

theorem different_coordinates_different_atoms (tag : I→A→Option T) (a a' : A)
    {i j : I} (neq : i≠j) : (tiedAtom (B:=B) tag a i)≠tiedAtom tag a' j :=
  fun h=>neq (congrArg Prod.snd h)

theorem untied_atom_distinct (tag : I→A→Option T) (i : I) {a a' : A}
    (h : a≠a') (d : ¬∃ z,tag i a=some z ∧ tag i a'=some z) :
    tiedAtom (B:=B) tag a i≠tiedAtom tag a' i := by
  cases ha : tag i a <;> cases hb : tag i a'
  · simp [tiedAtom,ha,hb,h]
  · simp [tiedAtom,ha,hb]
  · simp [tiedAtom,ha,hb]
  · intro he
    have heq := congrArg Prod.fst he
    simp only [tiedAtom,ha,hb,Option.elim_some,Sum.inl.injEq,Sum.inr.injEq] at heq
    exact d ⟨_,ha,heq ▸ hb⟩

def twoEdge (e f : E) (b : Bool) : E := if b then f else e

def selectedAtom (tag : I→A→Option T) (ar : E→A) (bc : E→B) (e f : E)
    (u : Bool×Bool×I) : Atom A B T I :=
  if u.2.1 then freeAtom (bc (twoEdge e f u.1)) u.2.2
  else tiedAtom tag (ar (twoEdge e f u.1)) u.2.2

theorem selectedAtom_injective (tag : I→A→Option T) (ar : E→A) (bc : E→B) (e f : E)
    (hr : ar e≠ar f) (hc : bc e≠bc f)
    (ht : ∀ i,¬∃ t,tag i (ar e)=some t ∧ tag i (ar f)=some t) :
    Function.Injective (selectedAtom tag ar bc e f) := by
  rintro ⟨x,b,i⟩ ⟨y,c,j⟩ h
  have hi : i=j := by
    have hcoord := congrArg Prod.snd h
    cases b <;> cases c <;> simpa only [selectedAtom,if_true,Bool.false_eq_true,if_false,
      freeAtom,tiedAtom] using hcoord
  subst j
  have hD := untied_atom_distinct (B:=B) tag i hr (ht i)
  cases b <;> cases c
  · have hb : x=y := by
      cases x <;> cases y
      · rfl
      · exact (hD h).elim
      · exact (hD h.symm).elim
      · rfl
    exact Prod.ext hb rfl
  · have hh := congrArg Prod.fst h
    simp [selectedAtom,tiedAtom,freeAtom] at hh
  · have hh := congrArg Prod.fst h
    simp [selectedAtom,tiedAtom,freeAtom] at hh
  · have hb : x=y := by
      cases x <;> cases y
      · rfl
      · exact (hc (Sum.inr.inj (congrArg Prod.fst h))).elim
      · exact (hc (Sum.inr.inj (congrArg Prod.fst h.symm))).elim
      · rfl
    exact Prod.ext hb rfl

end Key

section Expectation

open EmpiricalCutMoments
variable {A B T I S E : Type*}
variable [Fintype A] [Fintype B] [Fintype T] [Fintype I] [Fintype S] [Nonempty S]

theorem clean_cell_coincidence (tag : I→A→Option T) (ar : E→A) (bc : E→B) (e f : E)
    (hr : ar e≠ar f) (hc : bc e≠bc f)
    (ht : ∀ i,¬∃ t,tag i (ar e)=some t ∧ tag i (ar f)=some t) :
    mean (fun cfg : Atom A B T I→S => indicator
      (orderedCell tag ar bc cfg e=orderedCell tag ar bc cfg f))=1/(Fintype.card (Draw I S):ℚ) := by
  let key : Bool×Bool×I ↪ Atom A B T I :=
    ⟨selectedAtom tag ar bc e f,selectedAtom_injective tag ar bc e f hr hc ht⟩
  let Tail := {p // p∉Set.range key}→S
  letI : Fintype Tail := Fintype.ofFinite Tail
  letI : Nonempty Tail := ⟨fun _=>Classical.choice inferInstance⟩
  let split := chart (S:=S) key
  let h : (Bool→Draw I S)→ℚ := fun p=>indicator (p false=p true)
  let H : (Bool→Draw I S)×Tail→ℚ := fun p=>h p.1
  have point (cfg : Atom A B T I→S) (a : Bool) :
      (split cfg).1 a = orderedCell tag ar bc cfg (twoEdge e f a) := by
    apply Prod.ext
    · funext i
      exact (chart_first_of_key key cfg a i).1
    · funext i
      exact (chart_first_of_key key cfg a i).2
  have hfn : (fun cfg : Atom A B T I→S => indicator
      (orderedCell tag ar bc cfg e=orderedCell tag ar bc cfg f)) = fun cfg=>H (split cfg) := by
    funext cfg
    unfold H h
    rw [point cfg false,point cfg true]
    rfl
  rw [hfn,mean_equiv split H,show mean H=mean h from mean_extra h]
  exact independent_coincidence (D:=Draw I S) false true (by decide)

variable [Fintype E]

noncomputable def dependentPairs (tag : I→A→Option T) (ar : E→A) (bc : E→B) : Finset (E×E) :=
  Finset.univ.filter fun p=>ar p.1=ar p.2 ∨ bc p.1=bc p.2 ∨
    ∃ i t,tag i (ar p.1)=some t ∧ tag i (ar p.2)=some t

theorem expected_full_cell_deviation (tag : I→A→Option T) (ar : E→A) (bc : E→B) :
    mean (fun cfg : Atom A B T I→S=>deviation (orderedCell tag ar bc cfg))≤
      (dependentPairs tag ar bc).card := by
  apply expected_deviation_bad_pairs _ (dependentPairs tag ar bc)
  intro p hp
  have h : ¬ (ar p.1=ar p.2 ∨ bc p.1=bc p.2 ∨
      ∃ i t,tag i (ar p.1)=some t ∧ tag i (ar p.2)=some t) := by
    simpa only [dependentPairs,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  exact clean_cell_coincidence tag ar bc p.1 p.2 (fun x=>h (Or.inl x))
    (fun x=>h (Or.inr (Or.inl x))) (fun i ⟨t,x,y⟩=>h (Or.inr (Or.inr ⟨i,t,x,y⟩)))

end Expectation

#print axioms same_tag_same_symbol
#print axioms different_coordinates_different_atoms
#print axioms selectedAtom_injective
#print axioms clean_cell_coincidence
#print axioms expected_full_cell_deviation
end Paper5.HybridDOnly
