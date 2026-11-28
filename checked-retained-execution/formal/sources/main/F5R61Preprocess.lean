import F5R61PreprocessSchedule
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! The first F5 pass, from actual source literals to distinct new
physical variable tags, and the actual signed two-literal implications. -/
namespace F5R61.Preprocess
set_option autoImplicit false
set_option warningAsError true
open F5R59

variable {C V : Type} {n : ℕ} [DecidableEq V]
variable (S : ClauseSystem C V) (e : Fin n ≃ Vertex S)

abbrev EmittedClause := C ⊕ {x : Vertex S // active S e x}

def copied : ClauseSystem (EmittedClause S e) (Vertex S) where
  width
    | .inl c => S.width c
    | .inr _ => 2
  literal
    | .inl c, i => ⟨⟨c,i⟩,(S.literal c i).positive⟩
    | .inr x, i => if i.val=0 then ⟨x.val,false⟩ else ⟨successor S e x.val,true⟩

theorem keeps_original_literal (c : C) (i : Fin (S.width c)) :
    (copied S e).literal (.inl c) i = ⟨(⟨c,i⟩ : Vertex S),(S.literal c i).positive⟩ :=
  rfl

theorem emits_signed_cycle_clause (x : {x : Vertex S // active S e x}) :
    (copied S e).literal (.inr x) (0 : Fin 2) = ⟨x.val,false⟩ ∧
    (copied S e).literal (.inr x) (1 : Fin 2) = ⟨successor S e x.val,true⟩ ∧
    successor S e x.val ≠ x.val :=
  ⟨rfl,rfl,active_next_ne S e x.val x.property⟩

theorem copied_width2_or3 (h : ∀ c, S.width c = 2 ∨ S.width c = 3)
    (c : EmittedClause S e) :
    (copied S e).width c = 2 ∨ (copied S e).width c = 3 :=
  match c with
  | .inl c => h c
  | .inr _ => Or.inl rfl

theorem cycle_clause_iff (b : Vertex S → Bool) (x : {x : Vertex S // active S e x}) :
    (∃ i : Fin ((copied S e).width (.inr x)),
      b ((copied S e).literal (.inr x) i).var = ((copied S e).literal (.inr x) i).positive) ↔
    F5R60.Imp (b x.val) (b (successor S e x.val)) := by
  constructor
  · rintro ⟨i,h⟩ hx
    by_cases isZero : i.val=0
    · simp [copied,isZero,hx] at h
    · simpa [copied,isZero] using h
  · intro h
    cases hx : b x.val with
    | false => exact ⟨(0 : Fin 2),hx⟩
    | true => exact ⟨(1 : Fin 2),h hx⟩

/-- For an actual occurring name take the first physical tag. Names never
occurring in the source get false and are irrelevant to clause semantics. -/
def readOriginal (b : Vertex S → Bool) (v : V) : Bool :=
  if hn : 0 < (sameIndices S e v).card then b (fibreOrder S e v ⟨0,hn⟩).val else false

theorem read_returns_every_copy (b : Vertex S → Bool) (h : satisfies (copied S e) b)
    (x : Vertex S) : readOriginal S e b (Name S x) = b x := by
  have hn : 0 < (sameIndices S e (Name S x)).card :=
    Finset.card_pos.mpr ⟨_,(indexFibre S e (Name S x) ⟨x,rfl⟩).property⟩
  rw [readOriginal,dif_pos hn]
  apply active_cycles_force_one_value S e b
  · intro y yActive
    exact (cycle_clause_iff S e b ⟨y,yActive⟩).1 (h (.inr ⟨y,yActive⟩))
  · exact (fibreOrder S e (Name S x) ⟨0,hn⟩).property

theorem copied_satisfiable_iff :
    (∃ b, satisfies (copied S e) b) ↔ ∃ a, satisfies S a := by
  constructor
  · rintro ⟨b,h⟩
    refine ⟨readOriginal S e b, ?_⟩
    intro c
    obtain ⟨i,hi⟩ := h (.inl c)
    exact ⟨i,(read_returns_every_copy S e b h ⟨c,i⟩).trans hi⟩
  · rintro ⟨a,ha⟩
    refine ⟨fun x => a (Name S x),?_⟩
    intro c
    cases c with
    | inl c => exact ha c
    | inr x =>
      apply (cycle_clause_iff S e (fun x => a (Name S x)) x).2
      intro yes
      exact (congrArg a (next_same_name S e x.val)).trans yes

abbrev CopySlot := Vertex (copied S e)
abbrev Incidence (x : Vertex S) := {p : CopySlot S e // (term (copied S e) p).var = x}

/-- A genuine incident slot is of exactly one of these three kinds:
its own literal, its outgoing negative port, or its incoming positive port. -/
def place : CopySlot S e → Fin 3
  | ⟨.inl _,_⟩ => 0
  | ⟨.inr _,i⟩ => if i.val=0 then 1 else 2

private theorem slot_from_name_and_place {p q : CopySlot S e}
    (name : (term (copied S e) p).var = (term (copied S e) q).var)
    (kind : place S e p=place S e q) : p=q := by
  rcases p with ⟨c,i⟩
  rcases q with ⟨d,j⟩
  cases c with
  | inl a =>
    cases d with
    | inl b =>
      change (⟨a,i⟩ : Vertex S) = ⟨b,j⟩ at name
      exact congrArg (fun z : Vertex S => (⟨.inl z.1,z.2⟩ : CopySlot S e)) name
    | inr b =>
      by_cases j0 : j.val=0 <;> simp [place,j0] at kind
  | inr a =>
    cases d with
    | inl b =>
      by_cases i0 : i.val=0 <;> simp [place,i0] at kind
    | inr b =>
      by_cases i0 : i.val=0 <;> by_cases j0 : j.val=0
      · have ab : a=b := Subtype.ext (by simpa [term,copied,i0,j0] using name)
        subst b
        have ij : i=j := Fin.ext (i0.trans j0.symm)
        subst j
        rfl
      · simp [place,i0,j0] at kind
      · simp [place,i0,j0] at kind
      · have ab : a=b := Subtype.ext ((successor S e).injective (by
          simpa [term,copied,i0,j0] using name))
        subst b
        have hi : i.val<2 := i.isLt
        have hj : j.val<2 := j.isLt
        have ij : i=j := Fin.ext (by omega)
        subst j
        rfl

theorem each_copied_variable_at_most_three (x : Vertex S) :
    Nat.card (Incidence S e x) ≤ 3 := by
  have hinj : Function.Injective (fun z : Incidence S e x => place S e z.val) := by
    intro a b same
    exact Subtype.ext (slot_from_name_and_place S e (a.property.trans b.property.symm) same)
  simpa using Nat.card_le_card_of_injective _ hinj

theorem clause_physical_variables_distinct (c : EmittedClause S e) :
    Function.Injective (fun i : Fin ((copied S e).width c) => ((copied S e).literal c i).var) := by
  intro i j eq
  cases c with
  | inl c =>
    exact Fin.ext (congrArg (fun z : Vertex S => z.2.val) eq)
  | inr x =>
    by_cases i0 : i.val=0 <;> by_cases j0 : j.val=0
    · exact Fin.ext (i0.trans j0.symm)
    · exact False.elim (active_next_ne S e x.val x.property (by
        simpa [copied,i0,j0] using eq.symm))
    · exact False.elim (active_next_ne S e x.val x.property (by
        simpa [copied,i0,j0] using eq))
    · have hi : i.val<2 := i.isLt
      have hj : j.val<2 := j.isLt
      exact Fin.ext (by omega)

theorem preprocess_actual_width_three {m : ℕ} (S : ClauseSystem (Fin m) V)
    (width : ∀ c, S.width c = 3) :
    let ord := initialOrder S width
    let P := copied S ord
    (∀ c, P.width c=2 ∨ P.width c=3) ∧
    (∀ x, Nat.card {p : Vertex P // (term P p).var=x}≤3) ∧
    (∀ c, Function.Injective (fun i : Fin (P.width c) => (P.literal c i).var)) ∧
    ((∃ b, satisfies P b) ↔ ∃ a, satisfies S a) :=
  ⟨copied_width2_or3 S _ (fun c => Or.inr (width c)),
    each_copied_variable_at_most_three S _,clause_physical_variables_distinct S _,
    copied_satisfiable_iff S _⟩

#print axioms copied
#print axioms keeps_original_literal
#print axioms emits_signed_cycle_clause
#print axioms copied_width2_or3
#print axioms cycle_clause_iff
#print axioms readOriginal
#print axioms read_returns_every_copy
#print axioms copied_satisfiable_iff
#print axioms each_copied_variable_at_most_three
#print axioms clause_physical_variables_distinct
#print axioms preprocess_actual_width_three
end F5R61.Preprocess
