import J6R49CostActive
import J6R24MeteredRecursionNativeLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2800

/-! The whole active R49 child bill is a weighted sum over the actual
native slot type; the older complete list is only a proof of this
reindexing and is not an executable enumeration. -/
namespace J6R49Cost
open scoped Polynomial Classical
open AOracleMachineTime J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R49DFS

attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem stream_active_child_bill_matches_census
    {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    {q : ℕ} (D : @ActiveMachine f ell s sel c d bank q) (hv : 0<ell)
    (child : @ActiveChild f ell s sel c d bank) :
    streamActiveChildBill (sel:=sel) (d:=d) D child = D.prior.children hv child := by
  unfold streamActiveChildBill ActiveDesc.children
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  unfold centreChildBill J6R22Active.SiteTape.childBill
  apply congrArg List.sum
  apply List.map_congr_left
  intro z _
  exact (exact_probe_child_census (D.tape t).low (child t z) (D.prior.tape t).modes
    (D.prior.tape t).modeUnique (D.prior.tape t).modeComplete).1.symm

theorem stream_active_child_bill_matches_slots
    {sel : @Selector f ell S (sourceDelta s)}
    {c : Call (PhysicalHost f ell)} {d : @Ready f ell S (sourceDelta s) c} {bank : Bank f}
    {q : ℕ} (D : @ActiveMachine f ell s sel c d bank q) (hv : 0<ell)
    (child : @ActiveChild f ell s sel c d bank)
    (cost : (@Plan f ell s sel).Slot c → ℕ)
    (actual : ∀ t z β g,(child t z β g).steps=cost (addressed (sel:=sel) d t z β g)) :
    streamActiveChildBill (sel:=sel) (d:=d) D child=@Finset.sum ((@Plan f ell s sel).Slot c) ℕ _
      (@Finset.univ _ ((@Plan f ell s sel).finiteSlot c)) cost := by
  rw [stream_active_child_bill_matches_census (sel:=sel) (d:=d) D hv child]
  exact child_sum_exact (sel:=sel) d D.prior hv child cost actual

#print axioms stream_active_child_bill_matches_census
#print axioms stream_active_child_bill_matches_slots
end J6R49Cost

