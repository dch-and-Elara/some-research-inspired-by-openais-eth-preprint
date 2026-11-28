
import J6R52PeakReaderDefs
import J6R51PeakGeneratedSidecar

/-! At a true nonroot demand, the actual authored addon and indexed
sidecar tape are measured by the same paid acquisition phase, at
its own local snapshot. This is not a claim of a memoized across-slot
cache or that all arithmetic/allocator scratch is resident. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R48RawRoute J6R48GeneratedAddons
open J6R48DFS J6R50SourceProducer J6R51Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 21500000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem true_demand_sidecar_has_its_fee_and_selected_fields
    (M : OnlineMachine T key prec tw bw page q)
    (p : Path sel r c) (u : (P).Slot c) (w : (P).Slot ((P).child c u)) :
    let X := sourceState M p u
    let start := M.demand X w
    let K := start.result
    let booked := K.advance.next
    let B := booked.birth
    let S := booked.site
    let made := emit (K.directory.read X K.event) B.native.physical.order
    acquisitionAt M (.step p u) w = start.steps+(made.steps+S.install.steps) ∧
    S.install.result=some S.bank ∧
    made.result=S.input ∧
    (pairedAddonPayload S).length≤
      (2*((P).child c u).edges)*(B.port+
        2*addonCap K.directory.ow (dim (successorTicket (p.ticket u) w)) key prec page) := by
  let X := sourceState M p u
  let K := (M.demand X w).result
  have a := actual_generated_sidecar_selected_bits_and_fee X K.event K.directory
  exact ⟨rfl,a.1,a.2.1,a.2.2.1⟩

#print axioms true_demand_sidecar_has_its_fee_and_selected_fields
end
end J6R52Peak
