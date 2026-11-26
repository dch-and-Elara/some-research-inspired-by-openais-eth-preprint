import P5AlwaysSatOriginalTaylorProvider
import P5AlwaysSatOriginalTaylorExp

namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6
open scoped Classical BigOperators

/-- Independent review lemma: extending the retained order preserves the same
actual coefficient, the same chosen cuts and the same rank witness. -/
theorem audit_printedWitness_mono {V E W F Copy : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [Fintype W] [Fintype F] [Fintype Copy]
    {n C d d' ell : ℕ} {γ : ℚ} {ε : ℝ}
    {L : SourceLayout E W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n))}
    {mark : V↪E} {P : SourceRecipe L mark}
    (hd : d≤d') (h : PrintedWitness n C d ell γ ε L mark P) :
    PrintedWitness n C d' ell γ ε L mark P := by
  have hk : printedOrder n d ≤ printedOrder n d' := by
    unfold printedOrder
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_right _ hd)) 1
  obtain ⟨S,hs,g,hg,⟨⟨t,j⟩,v⟩,hj,hr⟩ := h
  refine ⟨S,hs,g,hg,⟨⟨t,⟨j.val,lt_of_lt_of_le j.isLt hk⟩⟩,v⟩,?_,?_⟩
  · exact hj
  · exact hr

theorem audit_direct_source_window {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Finset (V×V)) (T : Finset V) (D : DirectProvider E T) {γ : ℚ} {ε : ℝ}
    (h : DirectProvider.Hard E T D γ ε) :
    PrintedWitness (mainN E T) 54 (3*mainN E T) 1 γ ε D.layout
      (directChart D.layout (certificate_layout_owners D) (certificate_layout_factors D)).mark
      (directRecipe D.layout (certificate_layout_owners D) (certificate_layout_factors D)) := by
  apply audit_printedWitness_mono (d:=directDegree E T) _ h
  rw [actual_direct_degree]
  exact Nat.sub_le _ _

#print axioms audit_printedWitness_mono
#print axioms audit_direct_source_window
end Paper5.AlwaysSatOriginal.Physical.Taylor
