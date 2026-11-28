import F5R60PhysicalF1
import Mathlib.Tactic.FinCases

/-! The actual four clauses of a triple have separate keys. Equality
of logical names alone is not a within-clause forbidden adjacency. -/
namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false

variable {V E T : Type}

inductive OriginalClauseKey (V E T : Type)
  | vertexSwitch (v : V)
  | edgeConflict (e : E)
  | edgeRequest (e : E)
  | tripleClause (t : T) (which : Fin 4)

def tripleClausePart (i : Fin 10) : Fin 4 :=
  if i.val < 2 then 0 else if i.val < 4 then 1 else if i.val < 7 then 2 else 3

/-- The concrete clause owning this physical occurrence. In particular
OR-auxiliary positions 1,3,6,7 have four different owning clauses. -/
def originalClauseKey : PrivatePos V E T → OriginalClauseKey V E T
  | .sw v _ => .vertexSwitch v
  | .cf e _ => .edgeConflict e
  | .er e _ => .edgeRequest e
  | .tr d i => .tripleClause d (tripleClausePart i)

def RepeatInOriginalClause (G : RequestGraph V E T) (p q : PrivatePos V E T) : Prop :=
  nameOf G p = nameOf G q ∧ originalClauseKey p = originalClauseKey q ∧ p≠q

structure DistinctSourceEnds (G : RequestGraph V E T) : Prop where
  edge : ∀ e, G.left e ≠ G.right e
  triple : ∀ t, G.first t ≠ G.second t ∧ G.first t ≠ G.third t ∧ G.second t ≠ G.third t

/-- Exactly the three oriented shapes emitted by the source list builder. -/
inductive OriginalForwardPair : PrivatePos V E T → PrivatePos V E T → Prop
  | switch (v : V) : OriginalForwardPair (.sw v 0) (.sw v 1)
  | edge (e : E) : OriginalForwardPair (.er e 0) (.er e 2)
  | triple (t : T) : OriginalForwardPair (.tr t 8) (.tr t 9)

theorem forward_pair_repeated (G : RequestGraph V E T) {p q : PrivatePos V E T}
    (h : OriginalForwardPair p q) : RepeatInOriginalClause G p q := by
  cases h <;> exact ⟨rfl,rfl,by simp⟩

theorem repeated_original_swap (G : RequestGraph V E T) {p q : PrivatePos V E T}
    (h : RepeatInOriginalClause G p q) : RepeatInOriginalClause G q p :=
  ⟨h.1.symm,h.2.1.symm,h.2.2.symm⟩

private theorem switch_indices (i j : Fin 2) (nd : i≠j) :
    (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
  fin_cases i <;> fin_cases j <;> simp_all

private theorem conflict_indices (G : RequestGraph V E T) (e : E)
    (distinct : G.left e≠G.right e) (i j : Fin 2)
    (nm : nameOf G (.cf e i)=nameOf G (.cf e j)) : i=j := by
  have rev : G.right e≠G.left e := distinct.symm
  fin_cases i <;> fin_cases j <;> simp_all [nameOf]

private theorem edge_indices (G : RequestGraph V E T) (e : E)
    (distinct : G.left e≠G.right e) (i j : Fin 3)
    (nm : nameOf G (.er e i)=nameOf G (.er e j)) (nd : i≠j) :
    (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) := by
  have rev : G.right e≠G.left e := distinct.symm
  fin_cases i <;> fin_cases j <;> simp_all [nameOf]

set_option maxHeartbeats 3000000 in
private theorem triple_indices (G : RequestGraph V E T) (t : T)
    (distinct : G.first t≠G.second t) (i j : Fin 10)
    (cl : tripleClausePart i=tripleClausePart j)
    (nm : nameOf G (.tr t i)=nameOf G (.tr t j)) (nd : i≠j) :
    (i=8 ∧ j=9) ∨ (i=9 ∧ j=8) := by
  have rev : G.second t≠G.first t := distinct.symm
  fin_cases i <;> fin_cases j <;> simp_all [nameOf,tripleClausePart]

theorem original_repeat_iff_pair_shapes (G : RequestGraph V E T)
    (D : DistinctSourceEnds G) (p q : PrivatePos V E T) :
    RepeatInOriginalClause G p q ↔ OriginalForwardPair p q ∨ OriginalForwardPair q p := by
  constructor
  · rintro ⟨hn,hc,hd⟩
    cases p with
    | sw v i =>
      cases q with
      | sw w j =>
        have eq : v=w := OriginalClauseKey.vertexSwitch.inj hc
        subst w
        have nd : i≠j := fun same => hd (congrArg (PrivatePos.sw v) same)
        rcases switch_indices i j nd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl (.switch v)
        · exact Or.inr (.switch v)
      | cf e j => cases hc
      | er e j => cases hc
      | tr t j => cases hc
    | cf e i =>
      cases q with
      | sw v j => cases hc
      | cf f j =>
        have eq : e=f := OriginalClauseKey.edgeConflict.inj hc
        subst f
        exact False.elim (hd (congrArg (PrivatePos.cf e) (conflict_indices G e (D.edge e) i j hn)))
      | er f j => cases hc
      | tr t j => cases hc
    | er e i =>
      cases q with
      | sw v j => cases hc
      | cf f j => cases hc
      | er f j =>
        have eq : e=f := OriginalClauseKey.edgeRequest.inj hc
        subst f
        have nd : i≠j := fun same => hd (congrArg (PrivatePos.er e) same)
        rcases edge_indices G e (D.edge e) i j hn nd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl (.edge e)
        · exact Or.inr (.edge e)
      | tr t j => cases hc
    | tr t i =>
      cases q with
      | sw v j => cases hc
      | cf e j => cases hc
      | er e j => cases hc
      | tr s j =>
        have eq : t=s ∧ tripleClausePart i=tripleClausePart j :=
          OriginalClauseKey.tripleClause.inj hc
        obtain ⟨he,hpart⟩ := eq
        subst s
        have nd : i≠j := fun same => hd (congrArg (PrivatePos.tr t) same)
        rcases triple_indices G t (D.triple t).1 i j hpart hn nd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl (.triple t)
        · exact Or.inr (.triple t)
  · rintro (h|h)
    · exact forward_pair_repeated G h
    · exact repeated_original_swap G (forward_pair_repeated G h)

#print axioms forward_pair_repeated
#print axioms repeated_original_swap
#print axioms original_repeat_iff_pair_shapes
end F5R61
