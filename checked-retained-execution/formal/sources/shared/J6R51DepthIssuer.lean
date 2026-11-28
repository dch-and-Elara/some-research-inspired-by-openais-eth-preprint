import J6R50IntegrationSameRun
import J6R48DFSScope

/-! Collision-free physical key allocation for the actual live
ancestor stack. Only the parent depth key is incremented. The
chosen layout consumers must use the emitted key. -/
namespace J6R51
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R16ModeCost J6R50Integration
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R15ModeCost

open J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 9500000

theorem charged_child_depth_word {f : ℤ[X]} {ell s C k : ℕ}
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {r c : Call (PhysicalHost f ell)} (stable : Stable s C r)
    (fit : r.depth ≤ pathLimit s C) (p : Path sel r c) (u : (Plan sel).Slot c)
    (offset : ℕ) (capacity : offset+pathLimit s C<2^k)
    (pos : 0<k) (current : Word k) (keyAt : current.val=offset+c.depth) :
    (increment current).result.val=offset+((Plan sel).child c u).depth ∧
    (increment current).steps=13*k+4 := by
  have reach := (Path.step p u).reached
  have atMost := stable_path_depth_bound_from_start cfg sel reach stable fit
  have childDepth : ((Plan sel).child c u).depth=c.depth+1 := rfl
  rw [childDepth] at atMost ⊢
  have h : current.val+1<2^k := by omega
  obtain ⟨v,t⟩ := increment_exact pos current h
  exact ⟨by omega,t⟩

section Install
variable {key prec tw bw : ℕ} {D : Type*}
local notation "B" => Ledger key prec tw bw D
local notation "J" => Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D

def Reserved (bank : B) (current : Word key) : Prop :=
  bank.synced ∧ ∀ a ∈ bank.headers, a.id.val ≤ current.val

theorem next_actual_job_fresh (bank : B) (current : Word key) (j : J)
    (bounded : Reserved bank current)
    (next : j.identifier.val=current.val+1) : JobsReady bank [j] := by
  refine ⟨bounded.1,by simp,?_⟩
  intro jj hj a ha bad
  have q := bounded.2 a ha
  have e : jj=j := List.mem_singleton.mp hj
  have badv := congrArg Word.val (bad.trans (congrArg Job.identifier e))
  omega

theorem next_actual_job_preserves_reserved (bank : B) (current : Word key) (j : J)
    (bounded : Reserved bank current)
    (next : j.identifier.val=current.val+1) :
    (j.install bank).result.2=true ∧ Reserved (j.install bank).result.1 j.identifier := by
  have ready := next_actual_job_fresh bank current j bounded next
  have instr := next_job_exact bank j [] ready
  rw [instr.1]
  refine ⟨rfl, instr.2.1, ?_⟩
  intro a ha
  change a ∈ j.entry.result :: bank.headers at ha
  rcases List.mem_cons.mp ha with h | h
  · subst a
    exact le_rfl
  · have q := bounded.2 a h
    omega

#print axioms charged_child_depth_word
#print axioms next_actual_job_fresh
#print axioms next_actual_job_preserves_reserved
end Install
end J6R51
