import J6R51DepthIssuer

/-! One runtime bank reserves only its live ancestor IDs. Siblings may
reuse the emitted depth key because each scoped visit restores bank. -/
namespace J6R51
open scoped Polynomial
open Polynomial J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R15ModeCost J6R48DFS

open J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2950
set_option maxHeartbeats 10000000

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page

theorem scoped_stack_depth_header_bound
    (born : Births T key prec tw bw page) (initial : L)
    (offset : ℕ) (sync : initial.synced)
    (base : ∀ row ∈ initial.headers,row.id.val≤offset+r.depth)
    (issuance : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x),
      (born p u).job.identifier.val=offset+((Plan sel).child x u).depth)
    {x : Call (PhysicalHost f ell)} (p : Path sel r x) :
    (stackBank born initial p).synced ∧
      ∀ row ∈ (stackBank born initial p).headers,row.id.val≤offset+x.depth := by
  induction p with
  | root => exact ⟨sync,base⟩
  | @step par p w ih =>
    have d : ((Plan sel).child par w).depth=par.depth+1 := rfl
    refine ⟨after_jobs_synced (stackBank born initial p) ih.1 [(born p w).job],?_⟩
    intro row a
    change row ∈ (born p w).job.entry.result :: (stackBank born initial p).headers at a
    rcases List.mem_cons.mp a with h | h
    · subst row
      exact (issuance p w).le
    · have prior := ih.2 row h
      omega

theorem one_reserved_depth_schedule_implies_ready_on_stack
    (born : Births T key prec tw bw page) (initial : L) (offset : ℕ)
    (sync : initial.synced)
    (base : ∀ row ∈ initial.headers,row.id.val≤offset+r.depth)
    (issuance : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x),
      (born p u).job.identifier.val=offset+((Plan sel).child x u).depth) :
    ReadyOnStack born initial := by
  intro x p u
  have trunk := scoped_stack_depth_header_bound born initial offset sync base issuance p
  refine ⟨trunk.1,by simp,?_⟩
  intro jj hj a ha bad
  have bound := trunk.2 a ha
  have same : jj=(born p u).job := List.mem_singleton.mp hj
  have ident := (congrArg Word.val (bad.trans (congrArg Job.identifier same))).trans (issuance p u)
  have d : ((Plan sel).child x u).depth=x.depth+1 := rfl
  omega

#print axioms scoped_stack_depth_header_bound
#print axioms one_reserved_depth_schedule_implies_ready_on_stack
end J6R51
