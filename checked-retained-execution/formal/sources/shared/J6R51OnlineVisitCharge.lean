import J6R51OnlineVisitDefs
import J6R51OnlineVisitLocal

/-! Exact charges at the actual visited slot on the new threaded run.
This module is independent of the decoded-output induction and of
any uniform global envelope. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (Plan sel)

theorem state_of_selected_after
    (M : OnlineMachine T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (w : (@Plan f ell s sel).Slot ((@Plan f ell s sel).child c u)) :
    (M.demand (sourceState M p u) w).result.advance.next=sourceState M (.step p u) w := rfl

theorem actual_after_read_charge
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges) (B : L)
    (t : Center S ((Plan sel).child c u)) (z : Probe S ((Plan sel).child c u)) (β : NativeMenu (N sel) ((Plan sel).child c u) t) (g : Fin 64)
    (good : JobsReady B [(M.demand X
      (addressed (sel:=sel) (ready_reachable cfg sel ((Path.step p u)).reached T.rootStable a) t z β g)).result.advance.next.birth.job]) :
    let d := ready_reachable cfg sel ((Path.step p u)).reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let K := M.demand X w
    let nxt := K.result.advance.next
    let j := nxt.birth.job
    let out := runAfter M retire ((Plan sel).child c u) (Path.step p u) w nxt (afterOne B j)
    readAfter M retire p u X a B t z β g=
      ⟨out.result.1,paidAcquisition K+(publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ ∧
    out.result.2=afterOne B j := by
  let d := ready_reachable cfg sel ((Path.step p u)).reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let K := M.demand X w
  let nxt := K.result.advance.next
  let F := T.bank (registerPrecision S ((Plan sel).child c u) t) (register_positive d t)
  let fallback : Meter (Block F ell) := zeroM F.hp
  let step := fun y=>runAfter M retire ((Plan sel).child c u) (Path.step p u) w y
  constructor
  · have H := open_demand_from_ready K retire step fallback B good
    change project (openDemand K retire step fallback B)=_
    rw [H]
    rfl
  · exact inherited_run_restores_bank M retire ((Plan sel).child c u) (Path.step p u) w nxt _
#print axioms state_of_selected_after
#print axioms actual_after_read_charge
end
end J6R51Online
