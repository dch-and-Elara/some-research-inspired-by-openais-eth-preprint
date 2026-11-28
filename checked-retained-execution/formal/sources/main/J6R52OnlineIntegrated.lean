import J6R51OnlineCorrect
import J6R52OnlineFeeLedger

/-! Joint theorem about one execution. Its prepared selector, local
source inputs, stopping agreement, and machine tariff interface are
explicit; this is not compilation from a bare CNF. -/
namespace J6R51Online
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime J6ActiveRun J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R16ModeCost J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49Cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3350
set_option maxHeartbeats 18000000
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]

theorem same_selected_online_value_and_bill
    (M : OnlineMachine T key prec tw bw page q)
    (initial : PageBank f ell key prec tw bw page)
    (retire : PageJob f ell key prec tw bw page → ℕ)
    (legal : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial)
    (rootFit : r.depth≤pathLimit s C) :
    let out := runRoot M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1 =
      (sourceBlueprint sel r hf).program.run r ∧ out.result.2=initial ∧
    out.steps≤ ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
      levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (onlineOwn M retire initial) j := by
  have h := full_online_selected_source M initial retire legal leaves
  exact ⟨h.1,h.2,same_online_run_paid_ledger M retire initial legal rootFit⟩

#print axioms same_selected_online_value_and_bill
end J6R51Online
