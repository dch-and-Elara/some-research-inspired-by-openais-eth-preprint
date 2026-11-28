import J6R58ActivePrepJoin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! The one-time raw chart mount uses at most the same quadratic
physical scale as a single full table read. The count of rows need
not be the field size, only the maximal live prefix. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R55CachedLedger J6R51Online J6R57ActiveFee

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem printed_prefix_install_tariff (M : OnlineMachine T key prec tw bw page q)
    (K : ℕ) (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K)
    (B : MaskTable f.natDegree (min K (2^f.natDegree)) (min_le_right _ _)) :
    (installActiveChart M B (live_probe_prefix (T:=T) K cs)).steps≤6+K*(3*K+5) := by
  rw [install_active_chart_exact]
  have e : f.natDegree≤K := by simpa only [cfg.coefficient] using ws.field
  exact Nat.add_le_add_left (Nat.mul_le_mul (min_le_left _ _) (Nat.add_le_add_right
    (Nat.mul_le_mul_left 3 e) 5)) 6

#print axioms printed_prefix_install_tariff
end
end J6R58ActivePrep

