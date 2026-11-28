import J7FullWordAssembly

/-! The two J7 objectives before seating. -/
open scoped BigOperators Classical
namespace J7R13
open J7SourceLabels J7SourceConditioning J7FullWordCells J7FullWordAssembly
noncomputable section
local instance (priority := 100000) : DecidableEq Slot :=
  fun _ _ => Classical.propDecidable _

local instance (priority := 100000) {P R C : Type*} : DecidableEq (Block P R C) :=
  fun _ _ => Classical.propDecidable _

variable {A Pair Row Col W : Type*} [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]
variable {t : ℕ}

/-- The two original J7 objectives on one and the same labeling, before padding. -/
def JointScore (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) : ℚ :=
  varianceScore Finset.univ (law A (Fin t → A) Pair Row Col) (fullCell row col) z +
    varianceScore (pinWires Pair W) (law A (Fin t → A) Pair Row Col) (fullCell row col) z


#print axioms JointScore
end
end J7R13
