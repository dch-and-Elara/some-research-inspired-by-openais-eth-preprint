import J6R51OnlineRun

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
set_option maxHeartbeats 11400000
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

theorem open_demand_from_ready
    {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} {R : Type}
    (start : Meter (LocalLoad X u)) (retire : J→ℕ)
    (go : StoredSite T (successorTicket v u) key prec tw bw page→SM L R)
    (bad : Meter R) (B : L) (good : JobsReady B [start.result.advance.next.birth.job]) :
    let next := start.result.advance.next
    let job := next.birth.job
    let child := go next (afterOne B job)
    openDemand start retire go bad B=
      ⟨(child.result.1,B),paidAcquisition start+(publishFee B job.entry job.offset job.built+child.steps+retire job+4)⟩ := by
  let nr := start.result.advance.next
  exact congrArg (fun out : Meter (R×L)=>Meter.mk out.result (paidAcquisition start+out.steps))
    (paid_scope_exact retire nr.birth.job (go nr) bad B good)

#print axioms open_demand_from_ready
end
end J6R51Online