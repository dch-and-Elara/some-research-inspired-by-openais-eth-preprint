import J6R49CostActiveAddress
import J6R16ModeCostSite

/-! Exact address cardinality for the retained centres of the live
machine, including all sixty-four groups at each genuine mode.
This is only a census proof, not a stored catalogue. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS J6R49Cost
open J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)} {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f} {q : ℕ}

private noncomputable def menuFinite (t : Center S c) : Fintype (NativeMenu (N sel) c t) :=
  nativeMenuFinite (N sel) c t

theorem modes_times_exact_groups_are_the_plan_addresses
    (D : @ActiveMachine f ell s sel c d bank q) :
    (D.centres.map (fun t=>J9PrintedSchedule.probeCount c.edges (2^(@centreA f ell s c)) *
      Nat.card (NativeMenu (N sel) c t)*64)).sum=Nat.card ((@Plan f ell s sel).Slot c) := by
  classical
  letI (t : Center S c) : Fintype (NativeMenu (N sel) c t) := menuFinite t
  letI (t : Center S c) : Finite (Probe S c × NativeMenu (N sel) c t × Fin 64) := by infer_instance
  have eq := Nat.card_congr (liveEquiv (sel:=sel) d)
  change Nat.card (Σ t : Center S c, Probe S c × NativeMenu (N sel) c t × Fin 64)=
    Nat.card ((@Plan f ell s sel).Slot c) at eq
  rw [←eq,Nat.card_sigma,complete_list_sum D.centres D.centreUnique D.centreComplete]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Nat.card_prod,Nat.card_fin]
  ac_rfl

theorem retained_centre_count_le_grid
    (D : @ActiveMachine f ell s sel c d bank q) :
    D.centres.length≤2^((@centreA f ell s c)+1) := by
  have full : D.centres.toFinset=Finset.univ := by
    ext t
    simp only [List.mem_toFinset,D.centreComplete t,Finset.mem_univ]
  calc
    _=D.centres.toFinset.card := (List.toFinset_card_of_nodup D.centreUnique).symm
    _=Nat.card (Center S c) := by rw [full,Finset.card_univ,Nat.card_eq_fintype_card]
    _≤_ := centers_le S c

#print axioms modes_times_exact_groups_are_the_plan_addresses
#print axioms retained_centre_count_le_grid
end J6R57ActiveFee
