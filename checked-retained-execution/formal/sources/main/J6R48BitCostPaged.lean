import J6R48BitCostPlan
import J6R33StatefulArithmeticPageDepth

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7500000
set_option maxRecDepth 2400

/-! Transfer the concrete internal arithmetic meter to the same R33
paged runtime. This leaves its writer/reader and leaf extras exactly as
the live chronology measures them. No registry state is reset. -/
namespace J6R48BitCost
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R22Active J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
attribute [local irreducible] J6R12Blueprint.printedParams

theorem actual_paged_arithmetic_bill
    {cfg : RootBounds s C f} {sel : @Selector f ell S (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic}
    {T : @Prepared f ell s C cfg sel r hf}
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    (R : @PagedResident f ell s C cfg sel r hf T key prec tw bw page) (d₀ : r.depth=0)
    (B : PageBank f ell key prec tw bw page) (ready : JobsReady B (pagedLog R r .root).jobs)
    (live : R.rootLive B) :
    let out := nativePaged R r .root B
    let log := pagedLog R r .root
    (T.frame (.reflexive r)).decode out.result.1=reduce r.prec f ell (r.host.contract hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps≤(∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (structuralAt T) j)+
        chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨val,bank,fee⟩ := whole_paged_depth R d₀ B ready live
  refine ⟨val,bank,?_⟩
  rw [fee]
  exact Nat.add_le_add_right (Nat.add_le_add_right (structural_depth_charge T) _) _

#print axioms actual_paged_arithmetic_bill
end J6R48BitCost

