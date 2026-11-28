import ACompactLayoutDiagonal

/-! The planted A4 ports from actual compact bipartite degree-2/3
incidence permutations. No row-label assignment or hard-incidence
matching certificate is taken as input: both come from those permutations. -/

namespace ACompactLayout
open Acquisition

structure CompactIncidence (m n₂ n₃ : ℕ) where
  onTwo : (Fin n₂ × Fin 2) ≃ Fin m
  onThree : (Fin n₃ × Fin 3) ≃ Fin m

abbrev Intended (m n₃ : ℕ) := Fin m ⊕ Fin n₃
abbrev HardPort (n₂ n₃ : ℕ) :=
  (Fin n₂ × Fin 2) ⊕ ((Fin n₃ × (Fin 3 ⊕ Unit)) ⊕ Fin n₃)

variable {m n₂ n₃ : ℕ} (g : CompactIncidence m n₂ n₃)

theorem incidence_sum (graph : CompactIncidence m n₂ n₃) : 2*n₂+3*n₃=2*m := by
  have h₂ := Fintype.card_congr graph.onTwo
  have h₃ := Fintype.card_congr graph.onThree
  simp only [Fintype.card_prod,Fintype.card_fin] at h₂ h₃
  omega

theorem cubic_even (graph : CompactIncidence m n₂ n₃) : Even n₃ :=
  odd_vertex_count_even (incidence_sum graph)

/-- Edge uses are one degree-two and one degree-three incidence.
An auxiliary's two uses are the negative clause's fourth port and the
positive unary pin. -/
def markedPort : Intended m n₃ × Bool → HardPort n₂ n₃
  | (.inl e,false) => .inl (g.onTwo.symm e)
  | (.inl e,true) => .inr (.inl ((g.onThree.symm e).1,.inl (g.onThree.symm e).2))
  | (.inr a,false) => .inr (.inl (a,.inr ()))
  | (.inr a,true) => .inr (.inr a)

def portUse : HardPort n₂ n₃ → Intended m n₃ × Bool
  | .inl z => (.inl (g.onTwo z),false)
  | .inr (.inl (v,.inl j)) => (.inl (g.onThree (v,j)),true)
  | .inr (.inl (v,.inr _)) => (.inr v,false)
  | .inr (.inr v) => (.inr v,true)

def incidenceOrder : Intended m n₃ × Bool ≃ HardPort n₂ n₃ where
  toFun := markedPort g
  invFun := portUse g
  left_inv := by
    rintro ⟨(e|a),b⟩ <;> cases b <;> simp [markedPort,portUse]
  right_inv := by
    rintro (z|(⟨a,j⟩|v))
    · simp [markedPort,portUse]
    · rcases j with j|j
      · simp [markedPort,portUse]
      · cases j
        rfl
    · rfl

def hardOccurrence (U : Type*) : HardPort n₂ n₃ → CoverOccurrences (Fin n₂) (Fin n₃) U
  | .inl (a,j) => ⟨.inl a,j⟩
  | .inr (.inl (a,j)) => ⟨.inr (.inl a),j⟩
  | .inr (.inr a) => ⟨.inr (.inr (.inl a)),()⟩

def sourceColumn {C : Type*} : Intended m n₃ → CoverCol (Fin m) (Fin n₃) C
  | .inl e => .inl e
  | .inr a => .inr (.inl a)

/-- This is the actual frozen signed-clause incidence function,
including the positive unary row, not a copy of the physical relation. -/
theorem markedPort_literal {U C : Type*} (stray : U → Option C)
    (i : Intended m n₃ × Bool) :
    let o := hardOccurrence U (markedPort g i)
    coverSources (fun a j => g.onTwo (a,j)) (fun a j => g.onThree (a,j)) stray o.1 o.2 =
      some (sourceColumn i.1) := by
  dsimp only
  rcases i with ⟨(e|a),b⟩ <;> cases b <;>
    simp [markedPort,hardOccurrence,sourceColumn,coverSources]

def useIndex (m n₃ : ℕ) : Intended m n₃ × Bool ≃ Fin (2*(m+n₃)) :=
  ((Equiv.prodCongr finSumFinEquiv finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm _ _))

theorem compact_planted_matches {U C : Type*} (stray : U → Option C)
    (i : Intended m n₃ × Bool)
    (active : 1 ≤ J9PrintedSchedule.rootU (lambda (3*(2*(m+n₃))))) :
    let j := useIndex m n₃ i
    let seat := printedDiagonalSeat (2*(m+n₃))
    let o := hardOccurrence U (markedPort g i)
    AAcquisitionCost.wirePred seat (.inl (j,true)) = some (.inl (j,false)) ∧
      coverSources (fun a p => g.onTwo (a,p)) (fun a p => g.onThree (a,p))
        stray o.1 o.2 = some (sourceColumn i.1) :=
  ⟨printedDiagonal_pred _ active _,markedPort_literal g stray i⟩

#print axioms incidence_sum
#print axioms cubic_even
#print axioms markedPort_literal
#print axioms compact_planted_matches

end ACompactLayout
