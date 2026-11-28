import J1PhysicalIndependent
import J1PhysicalIncidence
import ClonedWitness
import Mathlib.Tactic

/-! The actual reserved internal edge and unavailable exterior mates give
the two opposite literal-CNF answers, on the same diagonal pattern. -/
namespace J1PhysicalWitness
open J1PhysicalHost J1PhysicalIndependent MainClonedCNF PinnedWitness
variable {B : Type*} [Fintype B] [DecidableEq B]

def p (b : B) : Vertex B := (b,0)
def q (b : B) : Vertex B := (b,1)

private theorem exterior_right (M : Match B) (b : B) (H : Finset (Vertex B))
    (hH : H ⊆ available M b) (e : Vertex B × Vertex B) (he : e ∈ exterior M)
    (hr : e.1=p b ∨ e.1=q b) :
    e.2∉H ∧ e.2≠p b ∧ e.2≠q b := by
  have hx : e.1.1=b := by
    rcases hr with h|h <;> simp [h,p,q]
  have hmate : e.2=M.mate e.1 := (mem_exterior M _ _).mp he |>.1
  have hn := (unavailable_at_reserved M b H hH e.1 hx).2
  refine ⟨by rw [hmate]; exact hn,?_,?_⟩
  · intro hEq
    exact M.cross e.1 ((congrArg Prod.fst hmate).symm.trans
      ((congrArg Prod.fst hEq).trans hx.symm))
  · intro hEq
    exact M.cross e.1 ((congrArg Prod.fst hmate).symm.trans
      ((congrArg Prod.fst hEq).trans hx.symm))

private theorem exterior_left (M : Match B) (b : B) (H : Finset (Vertex B))
    (hH : H ⊆ available M b) (e : Vertex B × Vertex B) (he : e ∈ exterior M)
    (hr : e.2=p b ∨ e.2=q b) :
    e.1∉H ∧ e.1≠p b ∧ e.1≠q b := by
  have hx : e.2.1=b := by
    rcases hr with h|h <;> simp [h,p,q]
  have hmate : e.1=M.mate e.2 := (exterior_adjacent M e.2 e.1).mp (Or.inr he)
  have hn := (unavailable_at_reserved M b H hH e.2 hx).2
  refine ⟨by rw [hmate]; exact hn,?_,?_⟩
  · intro hEq
    exact M.cross e.2 ((congrArg Prod.fst hmate).symm.trans
      ((congrArg Prod.fst hEq).trans hx.symm))
  · intro hEq
    exact M.cross e.2 ((congrArg Prod.fst hmate).symm.trans
      ((congrArg Prod.fst hEq).trans hx.symm))

theorem opposite_actual_formulas (M : Match B) (b : B) (P : Finset (Vertex B))
    (hP : P ⊆ available M b) (hI : Independent M P) (w : Vertex B → Bool) :
    let E := edges M
    PinnedCNF.modelCount (J1PhysicalIncidence.compiledCNF E (degree_eq_three M) (enabled P w)) = 1 ∧
    PinnedCNF.modelCount (J1PhysicalIncidence.compiledCNF E (degree_eq_three M)
      (disabled P w (p b) (q b))) = 0 := by
  simp only
  rw [J1PhysicalIncidence.literal_to_original_formula,J1PhysicalIncidence.literal_to_original_formula]
  have hi : (p b,q b) ∈ interior B := (mem_interior _ _).mpr rfl
  exact ClonedWitness.paired_literal_count (interior B) (exterior M) P (p b) (q b) w
    (leftSlot (edges M) (degree_eq_three M)) (rightSlot (edges M) (degree_eq_three M))
      (graph_independent M P hI) hi
      (unavailable_at_reserved M b P hP (p b) rfl).1
      (unavailable_at_reserved M b P hP (q b) rfl).1
      (exterior_right M b P hP) (exterior_left M b P hP)

#print axioms opposite_actual_formulas

end J1PhysicalWitness
