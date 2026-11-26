import P5HybridDOnlyKey

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 16

/-! Selection in the finite atom space and explicit Fintype transport. -/
namespace Paper5.HybridDOnly
open scoped Classical BigOperators
open J1MainSourceCollision DiagonalAbundance

attribute [local irreducible] J1MainSourceCollision.deviation

theorem transport_deviation_chart {E C : Type*}
    {srcE dstE : Fintype E} {srcC dstC : Fintype C}
    (g : E→C) (b : ℚ) (h : @deviation E C srcE srcC g≤b) :
    @deviation E C dstE dstC g≤b := by
  letI : Subsingleton (Fintype E) := Fintype.subsingleton _
  letI : Subsingleton (Fintype C) := Fintype.subsingleton _
  have hE : srcE=dstE := Subsingleton.elim _ _
  have hC : srcC=dstC := Subsingleton.elim _ _
  cases hE
  cases hC
  exact h
section Outcome
variable {A B T I S E : Type*}
variable [Fintype A] [Fintype B] [Fintype T] [Fintype I] [Fintype S] [Nonempty S] [Fintype E]

theorem chosen_cell_score (tag : I→A→Option T) (ar : E→A) (bc : E→B) :
    ∃ cfg : Atom A B T I→S,
      deviation (orderedCell tag ar bc cfg)≤(dependentPairs tag ar bc).card := by
  let g := fun cfg : Atom A B T I→S => deviation (orderedCell tag ar bc cfg)
  obtain ⟨z,hz⟩ := Paper5.HybridClosure.mean_le_select g
  exact ⟨z,hz.trans (expected_full_cell_deviation (S:=S) tag ar bc)⟩
theorem chosen_cell_score_of_cap (tag : I→A→Option T) (ar : E→A) (bc : E→B)
    (bound : ℚ) (cap : ((dependentPairs tag ar bc).card:ℚ)≤bound) :
    ∃ cfg : Atom A B T I→S, deviation (orderedCell tag ar bc cfg)≤bound := by
  obtain ⟨cfg,h⟩ := chosen_cell_score (S:=S) tag ar bc
  exact ⟨cfg,h.trans cap⟩

/-- Only the graph function matters. In particular the generic coordinate
carrier and the concrete Fin chart can choose different definitional
Fintype instances without causing the kernel to enumerate their product. -/
theorem chosen_cell_score_with_chart (tag : I→A→Option T) (ar : E→A) (bc : E→B)
    (chart : Fintype (Draw I S)) (bound : ℚ) (cap : ((dependentPairs tag ar bc).card:ℚ)≤bound) :
    ∃ cfg : Atom A B T I→S,
      @deviation E (Draw I S) ‹Fintype E› chart (orderedCell tag ar bc cfg)≤bound := by
  obtain ⟨cfg,h⟩ := chosen_cell_score_of_cap (S:=S) tag ar bc bound cap
  exact ⟨cfg,@transport_deviation_chart E (Draw I S) _ ‹Fintype E› _ chart
    (orderedCell tag ar bc cfg) bound h⟩
end Outcome

#print axioms chosen_cell_score
#print axioms transport_deviation_chart
#print axioms chosen_cell_score_of_cap
#print axioms chosen_cell_score_with_chart
end Paper5.HybridDOnly
