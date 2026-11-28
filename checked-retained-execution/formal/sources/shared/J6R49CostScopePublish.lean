import J6R48DFSScope

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000
set_option maxRecDepth 2500

/-! The actual paid paired publisher on one legal path. In particular
the fee includes installing this occurrence's child constructor and
header; a reused key on a retired sibling is not a zero-cost cache hit. -/
namespace J6R49Cost
open scoped Polynomial
open AOracleMachineTime
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "B" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def scopedPublishCharge (born : Births T key prec tw bw page) (initial : B)
    (path : Path sel r c) (slot : (Plan sel).Slot c) (retire : J → ℕ) : ℕ :=
  let j := (born path slot).job
  publishFee (stackBank born initial path) j.entry j.offset j.built+retire j+4

theorem actual_ready_scope_edge_steps {A : Type*}
    (born : Births T key prec tw bw page) (initial : B)
    (path : Path sel r c) (slot : (Plan sel).Slot c) (valid : ReadyOnStack born initial)
    (retire : J → ℕ) (runChild : SM B A) (fallback : Meter A) :
    (withScope retire (born path slot).job runChild fallback (stackBank born initial path)).steps =
      scopedPublishCharge born initial path slot retire+
        (runChild (stackBank born initial (.step path slot))).steps := by
  rw [paid_scope_exact retire (born path slot).job runChild fallback _ (valid path slot)]
  unfold scopedPublishCharge
  dsimp only
  rw [show stackBank born initial (.step path slot)=
    afterOne (stackBank born initial path) (born path slot).job from rfl]
  omega

#print axioms scopedPublishCharge
#print axioms actual_ready_scope_edge_steps
end J6R49Cost

