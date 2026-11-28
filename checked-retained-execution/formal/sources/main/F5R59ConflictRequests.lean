import F5R59ConflictCore
import Std.Tactic

/-! The exact edge/triple request data for the F5 post-copy clauses.
Two-clause requests refer to two actual vertices and their clique edge.
Three-clause requests refer to three distinct occurrence vertices.
Ambient graph and the physical CNF compiler are independent later steps. -/

namespace F5R59
set_option autoImplicit false

variable {C V : Type} (S : ClauseSystem C V)

def atTwo (c : C) (w : S.width c = 2) (i : Fin 2) : Vertex S :=
  ⟨c, Fin.cast w.symm i⟩

def atThree (c : C) (w : S.width c = 3) (i : Fin 3) : Vertex S :=
  ⟨c, Fin.cast w.symm i⟩

theorem atTwo_edge (c : C) (w : S.width c = 2) :
    conflict S (atTwo S c w 0) (atTwo S c w 1) := by
  refine ⟨?_, Or.inl rfl⟩
  intro eq
  have e := congrArg (fun x : Vertex S => x.snd.val) eq
  exact (by decide : (0 : Nat) ≠ 1) e

theorem atThree_clique (c : C) (w : S.width c = 3) (i j : Fin 3) (hn : i ≠ j) :
    conflict S (atThree S c w i) (atThree S c w j) := by
  refine ⟨?_, Or.inl rfl⟩
  intro eq
  have e := congrArg (fun x : Vertex S => x.snd.val) eq
  exact hn (Fin.ext e)

theorem triple_requests_disjoint (c d : C) (hc : S.width c = 3) (hd : S.width d = 3)
    (ne : c ≠ d) (i j : Fin 3) : atThree S c hc i ≠ atThree S d hd j :=
  fun eq => ne (congrArg Sigma.fst eq)

def hitsPrintedRequests (I : Vertex S → Prop) : Prop :=
  (∀ c (w : S.width c = 2), I (atTwo S c w 0) ∨ I (atTwo S c w 1)) ∧
  (∀ c (w : S.width c = 3), I (atThree S c w 0) ∨
       I (atThree S c w 1) ∨ I (atThree S c w 2))

theorem printed_requests_hit_iff (widths : ∀ c, S.width c = 2 ∨ S.width c = 3)
    (I : Vertex S → Prop) :
    hitsPrintedRequests S I ↔ meetsClauses S I := by
  constructor
  · intro h c
    rcases widths c with e | e
    · rcases h.1 c e with q | q
      · exact ⟨Fin.cast e.symm 0,q⟩
      · exact ⟨Fin.cast e.symm 1,q⟩
    · rcases h.2 c e with q | q | q
      · exact ⟨Fin.cast e.symm 0,q⟩
      · exact ⟨Fin.cast e.symm 1,q⟩
      · exact ⟨Fin.cast e.symm 2,q⟩
  · intro h
    constructor
    · intro c e
      obtain ⟨a,ha⟩ := h c
      let i : Fin 2 := Fin.cast e a
      have same : I (atTwo S c e i) := by simpa [atTwo, i] using ha
      have k : i = 0 ∨ i = 1 := by
        have bound := i.isLt
        by_cases z : i.val = 0
        · exact Or.inl (Fin.ext z)
        · right
          apply Fin.ext
          change i.val = 1
          omega
      rcases k with z | z
      · exact Or.inl (z ▸ same)
      · exact Or.inr (z ▸ same)
    · intro c e
      obtain ⟨a,ha⟩ := h c
      let i : Fin 3 := Fin.cast e a
      have same : I (atThree S c e i) := by simpa [atThree, i] using ha
      have k : i = 0 ∨ i = 1 ∨ i = 2 := by
        have bound := i.isLt
        by_cases z : i.val = 0
        · exact Or.inl (Fin.ext z)
        · right
          by_cases o : i.val = 1
          · exact Or.inl (Fin.ext o)
          · right
            apply Fin.ext
            change i.val = 2
            omega
      rcases k with z | z | z
      · exact Or.inl (z ▸ same)
      · exact Or.inr (Or.inl (z ▸ same))
      · exact Or.inr (Or.inr (z ▸ same))

theorem decision_equivalence_for_printed_requests
    (widths : ∀ c, S.width c = 2 ∨ S.width c = 3) :
    (∃ a, satisfies S a) ↔ ∃ I, isIndependent S I ∧ hitsPrintedRequests S I := by
  rw [decision_equivalence]
  constructor
  · rintro ⟨I,hi,hm⟩
    exact ⟨I,hi,(printed_requests_hit_iff S widths I).2 hm⟩
  · rintro ⟨I,hi,hm⟩
    exact ⟨I,hi,(printed_requests_hit_iff S widths I).1 hm⟩

#print axioms atTwo_edge
#print axioms atThree_clique
#print axioms triple_requests_disjoint
#print axioms printed_requests_hit_iff
#print axioms decision_equivalence_for_printed_requests
end F5R59
