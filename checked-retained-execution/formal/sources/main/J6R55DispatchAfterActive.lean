import J6R55DispatchActive
import J6R51OnlineVisitEq

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! A descendant dispatch is bound to the precise `readAfter`
callback of the online machine. The equality hypothesis is only the
selected local acquisition meter, not a supplied value, child run,
or publication tariff. -/
namespace J6R55Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R50SourceProducer J6R32StatefulArithmetic
open J6R16ModeCost
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
theorem same_raw_active_phase_of_the_genuine_recursive_run
    {parent : Call (PhysicalHost f ell)} (p : Path sel root parent) (u : (Plan sel).Slot parent)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child parent u).edges)
    {rate : ℕ}
    (M : OnlineMachine T key prec tw bw page rate) (retire : PageJob f ell key prec tw bw page→ℕ)
    (B : PageBank f ell key prec tw bw page)
    (read : RawActiveChild sel (ready_reachable cfg sel (Path.step p u).reached T.rootStable on) T.bank rate)
    (same :
      let d := ready_reachable cfg sel (Path.step p u).reached T.rootStable on
      let A := M.activeAfter p u X on
      ∀ t z β g,read t z ((vectorKey sel d t (A.result.tape t).tape.result β).map J6R15ModeCost.word) g=
        readAfter M retire p u X on B t z β g) :
    let A := M.activeAfter p u X on
    let raw := evalRaw A.result M.modeWidth (reachable_positive T (Path.step p u).reached) T.vPositive hf read
    runAfter M retire parent p u X B=⟨(raw.result,B),A.steps+raw.steps⟩ := by
  let A := M.activeAfter p u X on
  have h := raw_active_is_same_meter A.result M.modeWidth
    (reachable_positive T (Path.step p u).reached) T.vPositive hf read (readAfter M retire p u X on B) same
  rw [run_after_active_eq M retire p u X on B]
  dsimp only
  rw [h]

#print axioms same_raw_active_phase_of_the_genuine_recursive_run
end
end J6R55Dispatch
