import J6R57ActiveFeeSplit
import J6R57ActiveFeeCensus
import J6R55CachedLedgerCore

/-! The native mode charge is paid by the same literal slot census
as the scoped callbacks. The fixed per-active-node meter is separate. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R23ScheduleWeight J6R19Retained HermiteLoss J6R48BitCost J6R49DFS J6R49Cost
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online
open J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 3300
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R12Blueprint.printedParams

private theorem map_sum_order {A : Type*} (l : List A) (u v : A→ℕ)
    (h : ∀ a∈l,u a≤v a) : (l.map u).sum≤(l.map v).sum := by
  induction l with
  | nil => exact le_rfl
  | cons a xs ih =>
    exact Nat.add_le_add (h a List.mem_cons_self) (ih (fun x hx=>h x (List.mem_cons_of_mem _ hx)))

private theorem map_sum_factor {A : Type*} (l : List A) (u : A→ℕ) (v : ℕ) :
    (l.map (fun x=>u x*v)).sum=(l.map u).sum*v := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.add_mul]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f} {q : ℕ}

theorem active_arithmetic_charged_against_actual_slots
    (D : ActiveMachine sel d bank q) (hp : 0<c.prec) (hv : 0<ell) (k : ℕ)
    (one : ∀ t∈D.centres,unitMode (D.tape t).low (D.tape t).tape.result≤64*k) :
    streamActiveTariff D hp hv≤fixedActive D hp hv+k*Nat.card ((Plan sel).Slot c) := by
  rw [active_split]
  apply Nat.add_le_add_left
  let b := fun (t : Center (printedParams (f:=f) (ell:=ell) s) c) =>
    (@probeCount f ell s c*Nat.card (NativeMenu (N sel) c t))
  calc
    _≤(D.centres.map (fun t=>b t*(64*k))).sum :=
      map_sum_order D.centres _ _ (fun t ht=>Nat.mul_le_mul_left _ (one t ht))
    _=(D.centres.map (fun t=>b t*64)).sum*k := by
      simp only [←Nat.mul_assoc,map_sum_factor]
    _=k*Nat.card ((Plan sel).Slot c) := by
      rw [show (D.centres.map (fun t=>b t*64)).sum=Nat.card ((Plan sel).Slot c) from
        modes_times_exact_groups_are_the_plan_addresses D,Nat.mul_comm]

theorem actual_active_phase_from_its_split_bill
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (fixed unit : ℕ)
    (hbase :
      let A := preparedActive M p a
      cacheMountFee M p+A.steps+fixedActive A.result (reachable_positive T p.reached) T.vPositive≤fixed)
    (hone :
      let A := preparedActive M p a
      ∀ t∈A.result.centres,unitMode (A.result.tape t).low (A.result.tape t).tape.result≤64*unit) :
    let A := preparedActive M p a
    cacheMountFee M p+A.steps+streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive≤
      fixed+unit*Nat.card ((Plan sel).Slot c) := by
  let A := preparedActive M p a
  let hp := reachable_positive T p.reached
  have bound := active_arithmetic_charged_against_actual_slots A.result hp T.vPositive unit hone
  calc
    _≤cacheMountFee M p+A.steps+(fixedActive A.result hp T.vPositive+unit*Nat.card ((Plan sel).Slot c)) :=
      Nat.add_le_add_left bound _
    _≤_ := by
      rw [←Nat.add_assoc]
      exact Nat.add_le_add_right hbase _

#print axioms active_arithmetic_charged_against_actual_slots
#print axioms actual_active_phase_from_its_split_bill
end
end J6R57ActiveFee
