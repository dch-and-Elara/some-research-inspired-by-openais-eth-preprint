import J6R58ActivePrepBoot
import J6R58ActivePrepValues

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! Insert the single paid mask-table installation before the same
actual recursive cache visit. The whole execution does not pay or
rebuild the installed raw table again at each visited node. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R55CachedLedger J6R51Online J6R57ActiveFee
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R53PeakAddon

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q n : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {fit : n≤2^f.natDegree}
local notation "Job" => (PageJob f ell key prec tw bw page)
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "M" => (OnlineMachine T key prec tw bw page q)

def runMountedActiveChart (W : M) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (retire : Job→ℕ) (initial : Pg)
    (p : Path sel r c) : Meter (Block (T.frame p.reached) ell × Pg) :=
  (installActiveChart W B covers).bind (fun installed=>cacheVisitAt installed retire initial p)

theorem actual_run_mount_paid_once (W : M) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (retire : Job→ℕ) (initial : Pg) (p : Path sel r c) :
    let root := cacheVisitAt (withActiveChart W B covers) retire initial p
    runMountedActiveChart W B covers retire initial p=
      ⟨root.result,(6+n*(3*f.natDegree+5))+root.steps⟩ := by
  simp only [runMountedActiveChart,install_active_chart_exact,Meter.bind]

theorem original_active_words_unchanged (W : M) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (read : ActiveChild (sel:=sel)
      (d:=ready_reachable cfg sel p.reached T.rootStable a) T.bank) :
    let hfPos := reachable_positive T p.reached
    ((preparedActive (withActiveChart W B covers) p a).result.eval W.modeWidth hfPos T.vPositive hf read).result=
      ((preparedActive W p a).result.eval W.modeWidth hfPos T.vPositive hf read).result := by
  rw [exact_prepared_active]
  exact same_active_value hf B (covers ⟨c,p⟩ a) (preparedActive W p a).result
    W.modeWidth (reachable_positive T p.reached) T.vPositive read

#print axioms actual_run_mount_paid_once
#print axioms original_active_words_unchanged
end
end J6R58ActivePrep

