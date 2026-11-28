
import PinnedWitness
import MainClonedCNF

namespace ClonedWitness
open PinnedWitness

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The two shadow inputs in J2 are literal four-clone CNFs with exact
    model counts one and zero, not merely arbitrary Boolean output labels. -/
theorem paired_literal_count (M D : Finset (V × V)) (P : Finset V)
    (p q : V) (w : V → Bool) (left right : (M ∪ D : Finset (V × V)) → Fin 4)
    (hI : independentOn (M ∪ D) P)
    (hM : (p,q) ∈ M) (hp : p ∉ P) (hq : q ∉ P)
    (hDL : ∀ e ∈ D, (e.1 = p ∨ e.1 = q) →
      e.2 ∉ P ∧ e.2 ≠ p ∧ e.2 ≠ q)
    (hDR : ∀ e ∈ D, (e.2 = p ∨ e.2 = q) →
      e.1 ∉ P ∧ e.1 ≠ p ∧ e.1 ≠ q) :
    PinnedCNF.modelCount (MainClonedCNF.formula (M ∪ D) left right (enabled P w)) = 1 ∧
    PinnedCNF.modelCount (MainClonedCNF.formula (M ∪ D) left right (disabled P w p q)) = 0 := by
  classical
  obtain ⟨_, hm1, hd1, hm0, _⟩ := paired M D P p q w hI hM hp hq hDL hDR
  have h1 : PinnedCNF.AllEdges (M ∪ D) (enabled P w) := by
    intro e he
    rcases Finset.mem_union.mp he with hm | hd
    · exact hm1 e hm
    · exact hd1 e hd
  have h0 : ¬ PinnedCNF.AllEdges (M ∪ D) (disabled P w p q) := by
    intro h
    exact hm0 (fun e he => h e (Finset.mem_union_left _ he))
  simp only [MainClonedCNF.modelCount_cloned, PinnedCNF.count_eq_indicator, if_pos h1, if_neg h0, and_self]

#print axioms paired_literal_count
end ClonedWitness

