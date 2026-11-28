import F5R61Preprocess
import Mathlib.Data.Finite.Prod

/-! Exact source first-pass volume. Count original literal positions
and both signs of each genuinely emitted active cycle row separately. -/
namespace F5R61.Preprocess
set_option autoImplicit false
set_option warningAsError true
open F5R59

variable {C V : Type} {n : ℕ} [DecidableEq V]
variable (S : ClauseSystem C V) (e : Fin n ≃ Vertex S)

abbrev ActiveTag := {x : Vertex S // active S e x}

def splitEmittedPositions : CopySlot S e ≃ Vertex S ⊕ (ActiveTag S e × Fin 2) where
  toFun
    | ⟨.inl c,i⟩ => .inl ⟨c,i⟩
    | ⟨.inr x,i⟩ => .inr (x,i)
  invFun
    | .inl ⟨c,i⟩ => ⟨.inl c,i⟩
    | .inr (x,i) => ⟨.inr x,i⟩
  left_inv x := by
    rcases x with ⟨c,i⟩
    cases c <;> rfl
  right_inv x := by
    rcases x with ⟨c,i⟩ | ⟨x,i⟩ <;> rfl

omit [DecidableEq V] in
theorem physical_tag_count (ord : Fin n ≃ Vertex S) : Nat.card (Vertex S)=n :=
  (Nat.card_congr ord.symm).trans (Nat.card_fin n)

theorem active_tag_count_at_most : Nat.card (ActiveTag S e)≤n := by
  letI : Finite (Vertex S) := Finite.of_injective e.symm e.symm.injective
  exact (Nat.card_le_card_of_injective (fun x : ActiveTag S e => x.val) Subtype.val_injective).trans_eq
    (physical_tag_count S e)

theorem exact_emitted_literal_count :
    Nat.card (CopySlot S e)=n+2*Nat.card (ActiveTag S e) := by
  letI : Finite (Vertex S) := Finite.of_injective e.symm e.symm.injective
  rw [Nat.card_congr (splitEmittedPositions S e),Nat.card_sum,Nat.card_prod,
    Nat.card_fin,physical_tag_count S e]
  omega

theorem exact_emitted_clause_count [Finite C] :
    Nat.card (EmittedClause S e)=Nat.card C+Nat.card (ActiveTag S e) := by
  letI : Finite (Vertex S) := Finite.of_injective e.symm e.symm.injective
  exact Nat.card_sum

theorem first_pass_size_linear {m : ℕ} (S : ClauseSystem (Fin m) V)
    (width : ∀ c, S.width c=3) :
    let e := initialOrder S width
    Nat.card (Vertex S)=3*m ∧
      m≤Nat.card (EmittedClause S e) ∧ Nat.card (EmittedClause S e)≤4*m ∧
      3*m≤Nat.card (CopySlot S e) ∧ Nat.card (CopySlot S e)≤9*m := by
  let ord := initialOrder S width
  have tag := physical_tag_count S ord
  have act := active_tag_count_at_most S ord
  have lit := exact_emitted_literal_count S ord
  have cls := exact_emitted_clause_count S ord
  rw [Nat.card_fin] at cls
  change Nat.card (Vertex S)=3*m ∧
    m≤Nat.card (EmittedClause S ord) ∧ Nat.card (EmittedClause S ord)≤4*m ∧
    3*m≤Nat.card (CopySlot S ord) ∧ Nat.card (CopySlot S ord)≤9*m
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

#print axioms splitEmittedPositions
#print axioms physical_tag_count
#print axioms active_tag_count_at_most
#print axioms exact_emitted_literal_count
#print axioms exact_emitted_clause_count
#print axioms first_pass_size_linear
end F5R61.Preprocess
