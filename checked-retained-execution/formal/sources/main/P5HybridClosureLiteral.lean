import P5HybridClosureScan
import P5HybridClosureGraph

namespace Paper5.HybridClosure
open scoped BigOperators Classical

variable {V A B : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The typed group handles can be taken to be the coordinates of the
literal layout labels: the primitives merely prove that the needed
edges are monochromatic. -/
theorem literal_source_group_factorization (E : Finset (V×V))
    (cubic : ∀v,GraphCutMoments.degree E v=3) (loopless : ∀v,(v,v)∉E)
    (cM : V→A) (cD : E→B)
    (L_M : TriVertex V→A) (L_D : TriVertex V→B)
    (hM : ∀p,L_M p=mainPinColor cM p) (hD : ∀p,L_D p=dPinColor E cubic cD p) :
    ∃ (monoM : ∀e∈innerEdges V,L_M e.1=L_M e.2)
      (monoD : ∀e∈outerEdges E cubic,L_D e.1=L_D e.2), ∀σ,
      PinnedCNF.modelCount (MainClonedCNF.formula (replacedEdges E cubic)
        (MainClonedCNF.leftSlot _ (replaced_cubic E cubic loopless))
        (MainClonedCNF.rightSlot _ (replaced_cubic E cubic loopless)) σ) =
      (∏g : A,groupOperand (innerEdges V) L_M monoM g (σ ∘ Subtype.val))*
      (∏g : B,groupOperand (outerEdges E cubic) L_D monoD g (σ ∘ Subtype.val)) := by
  have hm := funext hM
  have hd := funext hD
  subst L_M
  subst L_D
  exact ⟨main_inner_monochromatic cM,d_outer_monochromatic E cubic cD,
    cross_method_count E cubic loopless cM cD _ _⟩

theorem word_time_linear_of_source_feasible (N Q r : ℕ) (hN : 0<N) (hQ : 0<Q)
    (hGroup : 2*Q*r^2≤4*N) :
    6*N+r+64+1≤7*N+65 := by
  by_cases hr : r≤1
  · omega
  have h₁ : 2*r≤r^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (by omega)
  have h₂ : 2*r^2≤2*Q*r^2 := by
    exact Nat.mul_le_mul_right _ (by omega)
  have h₃ := (Nat.mul_le_mul_left 2 h₁).trans (h₂.trans hGroup)
  omega

#print axioms literal_source_group_factorization
#print axioms word_time_linear_of_source_feasible
end Paper5.HybridClosure