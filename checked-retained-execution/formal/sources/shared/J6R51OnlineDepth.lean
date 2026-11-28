import J6R51DepthReady
import J6R51OnlineCore

/-! Close the scoped readiness theorem for a runner whose actual
issuance invokes the verified increment on its visible parent word.
Arbitrary legacy issuance and raw chart producers are not identified. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R16ModeCost J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R15ModeCost J6R48DFS J6R50SourceProducer J6R51

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 15000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)

theorem online_depth_issuance_and_stack
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (offset : ℕ) (current : Word key) (pos : 0<key)
    (cap : offset+pathLimit s C<2^key)
    (rootFit : r.depth≤pathLimit s C) (rootKey : current.val=offset+r.depth)
    (sync : initial.synced) (base : ∀ a∈initial.headers,a.id.val≤offset+r.depth)
    (startIds : ∀ w, (M.initial w).result.birth.job.identifier=(increment current).result)
    (loadedIds : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c)
      (u : (P).Slot c) (w : (P).Slot ((P).child c u)),
      (M.demand (sourceState M p u) w).result.event.issued =
        increment (sourceState M p u).birth.job.identifier) :
    ReadyOnStack (borns M) initial ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c),
      (borns M p u).job.identifier.val=offset+((P).child c u).depth) ∧
    (∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c)
      (u : (P).Slot c) (w : (P).Slot ((P).child c u)),
      (M.demand (sourceState M p u) w).result.event.issued.steps=13*key+4) := by
  have ids : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c),
      (sourceState M p u).birth.job.identifier.val=offset+((P).child c u).depth := by
    intro c p
    induction p with
    | root =>
      intro w
      change (M.initial w).result.birth.job.identifier.val=_
      rw [startIds w]
      exact (charged_child_depth_word cfg sel T.rootStable rootFit Path.root w
        offset cap pos current rootKey).1
    | step p u ih =>
      intro w
      change (M.demand (sourceState M p u) w).result.advance.next.birth.job.identifier.val=_
      rw [loaded_job_label,loadedIds p u w]
      exact (charged_child_depth_word cfg sel T.rootStable rootFit (.step p u) w
        offset cap pos _ (ih u)).1
  refine ⟨one_reserved_depth_schedule_implies_ready_on_stack (borns M) initial offset sync base
    (fun p w=>ids p w), (fun p w=>ids p w),?_⟩
  intro c p u w
  rw [loadedIds p u w]
  exact (charged_child_depth_word cfg sel T.rootStable rootFit (.step p u) w
    offset cap pos _ (ids p u)).2

#print axioms online_depth_issuance_and_stack
end J6R51Online
