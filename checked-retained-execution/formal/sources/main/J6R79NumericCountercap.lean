import J6R67UnifiedRateScope
import J6R57ScopeFeeBoundary

/-! A fixed source representation does not determine the actual selected
boot debit. For the numeric gate we require a genuine producer bound,
not merely width fits and all semantic replies. -/
namespace J6R79Numeric
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R55CachedLedger J6R57ScopeFee J6R67UnifiedRate

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4300

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

/-- The exact R67 charge bound includes the observed successful R51 boot. -/
theorem measuredScope_dominates_real_boot {M : Machine} {B : Pg}
    (F : MeasuredScopeInputs M B) (ptr : ℕ) (w : (P).Slot r) :
    (M.initial w).steps ≤ measuredPerScope F ptr := by
  refine (F.boot w).trans ?_
  unfold measuredPerScope derivedPerScope acquisitionCeiling primitiveAndFootprintBudget
  exact (Nat.le_add_right _ _).trans ((le_max_left _ _).trans (Nat.le_add_right _ _))

/-- Even with precisely the same selected source states at *all* paths,
the R68 numeric cap cannot follow from those states and structural inputs.
The family changes only the observable boot debit, not any produced row. -/
theorem no_numeric_gate_from_source_replies
    (M : Machine) (B : Pg) (w : (P).Slot r) (ptr fixed arithmetic scale exp : ℕ) :
    let limit := scale*2^exp
    let M' := padInitialDebit M (limit+1)
    (∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (P).Slot x),
      sourceState M' p u=sourceState M p u) ∧
    (∀ F : MeasuredScopeInputs M' B,
      ¬ fixed+(arithmetic+measuredPerScope F ptr) ≤ limit) := by
  dsimp only
  refine ⟨boot_fee_padding_keeps_all_real_source_states M _, ?_⟩
  intro F h
  have b := measuredScope_dominates_real_boot F ptr w
  change (M.initial w).steps+(scale*2^exp+1) ≤ measuredPerScope F ptr at b
  omega

#print axioms measuredScope_dominates_real_boot
#print axioms no_numeric_gate_from_source_replies
end
end J6R79Numeric
