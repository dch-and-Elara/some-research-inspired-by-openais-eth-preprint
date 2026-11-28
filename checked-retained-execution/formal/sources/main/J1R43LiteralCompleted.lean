import J1R43LiteralNative

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

/-! Original J1 completed root product. This applies to the exact printed
layout of `actual_checked_native` and never invents a separate assignment
of the diagonal readouts for separate groups. -/
namespace J1R43Literal
open scoped Polynomial BigOperators
open MainProbe J1R14Query

variable {I S X C P : Type*} [Fintype I] [DecidableEq I] [Fintype S] [LinearOrder S]
    [Fintype X] [DecidableEq X] [Fintype C] [Fintype P] [DecidableEq P]

theorem completed_requires_all_pins
    (D : DiagonalLayout I S X C P) (J : Finset ℕ) (h0 : 0∉J)
    (t : I) (E : Finset X) (y : RowValues S C (Exceptional I S J))
    (U : X→Bool) (sign : P→Bool) (f : ℚ[X]) (node : I→ℚ)
    (other : S→(X→Bool)→ℚ[X]) (p : P)
    (hwrong : sign p≠prescribed D (printedBasis D J h0) t y p) :
    sourceCompletedProbe D J f node t Finset.univ
      (fun g=>secondScan D (printedBasis D J h0) t g E y) U
      (prescribed D (printedBasis D J h0) t y) sign other=0 :=
  sourceCompletedProbe_off D J h0 f node t Finset.univ
    (fun g=>secondScan D (printedBasis D J h0) t g E y) U
    (prescribed D (printedBasis D J h0) t y) sign other p (Finset.mem_univ p) hwrong

#print axioms completed_requires_all_pins

end J1R43Literal