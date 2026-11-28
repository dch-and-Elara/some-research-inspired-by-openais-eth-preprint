import J6R58OrdinalSpacePulse
import J6R48DFSModeDrain

/-! Actual rank-bearing halt-driven fold. Only the live cursor, one
fixed-width ordinal and the callback accumulator persist between
emissions; the mathematical future sequence below is used solely
as a proof of termination and exact comparative fees. This module
does not model arbitrary callback closures or the allocator. -/
namespace J6R58OrdinalSpace
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply J6R48DFS
set_option autoImplicit false
set_option maxHeartbeats 14500000

variable {q n bits : ℕ} {A : Type*}

def rankedDrain (op : A→List (Word q)→Word bits→Meter A)
    (p : Pending q n) (clock : Word bits) (a : A) (fee : ℕ) : Meter (A×Bool) :=
  let z := p.pulse
  match e : z.result with
  | .again _ => ⟨(a,false),fee+z.steps⟩
  | .halt => ⟨(a,true),fee+z.steps⟩
  | .emit w _ =>
    let next := increment clock
    let out := op a w clock
    rankedDrain op (p.tail e) next.result out.result (fee+z.steps+next.steps+3+out.steps)
termination_by p.ghostLen
decreasing_by exact p.tail_smaller e

theorem ranked_drain_halts_at_the_same_real_event
    (op : A→List (Word q)→Word bits→Meter A) (p : Pending q n)
    (clock : Word bits) (a : A) (fee : ℕ) (h : p.pulse.result=.halt) :
    rankedDrain op p clock a fee=⟨(a,true),fee+p.pulse.steps⟩ := by
  rw [rankedDrain]
  dsimp only
  split
  · rename_i _ he
    rw [h] at he
    cases he
  · rfl
  · rename_i _ _ he
    rw [h] at he
    cases he

theorem ranked_drain_advances_one_actual_cursor_step
    (op : A→List (Word q)→Word bits→Meter A) (p : Pending q n) (clock : Word bits)
    (a : A) (fee : ℕ) {raw : List (Word q)} {st : State q}
    (e : p.pulse.result=.emit raw st) :
    rankedDrain op p clock a fee=
      rankedDrain op (p.tail e) (increment clock).result (op a raw clock).result
        (fee+p.pulse.steps+(increment clock).steps+3+(op a raw clock).steps) := by
  rw [rankedDrain]
  dsimp only
  split
  · rename_i _ he
    rw [e] at he
    cases he
  · rename_i he
    rw [e] at he
    cases he
  · rename_i _ _ he
    cases he.symm.trans e
    rfl

theorem old_drain_halt_or_emit (op : A→List (Word q)→Meter A)
    (p : Pending q n) (a : A) (fee : ℕ) :
    (p.pulse.result=.halt → modeDrain op p a fee=⟨(a,true),fee+p.pulse.steps⟩) ∧
    (∀ {raw st} (e : p.pulse.result=.emit raw st),
      modeDrain op p a fee=modeDrain op (p.tail e) (op a raw).result
        (fee+p.pulse.steps+(op a raw).steps)) := by
  constructor
  · intro h
    rw [modeDrain]
    dsimp only
    split
    · rename_i _ he
      rw [h] at he
      cases he
    · rfl
    · rename_i _ _ he
      rw [h] at he
      cases he
  · intro raw st e
    rw [modeDrain]
    dsimp only
    split
    · rename_i _ he
      rw [e] at he
      cases he
    · rename_i he
      rw [e] at he
      cases he
    · rename_i _ _ he
      cases he.symm.trans e
      rfl

theorem fixed_width_traversal_adds_one_rank_increment_per_real_emission
    (pos : 0<bits) (op : A→List (Word q)→Meter A)
    (p : Pending q n) (clock : Word bits) (a : A) (fee : ℕ)
    (xs : List (List ℕ)) (trace : Runs n p.state xs (.ascend []))
    (room : clock.val+xs.length<2^bits) :
    rankedDrain (fun a raw _=>op a raw) p clock a fee=
      modeDrain op p a (fee+xs.length*(13*bits+7)) := by
  induction xs generalizing p clock a fee with
  | nil =>
    have shape := (one_paid_event p.state p.valid [] trace).1
    change NextExact n [] p.pulse.result at shape
    cases now : p.pulse.result with
    | again st => exact (p.no_again now).elim
    | halt =>
      rw [ranked_drain_halts_at_the_same_real_event _ _ _ _ _ now,
        List.length_nil,Nat.zero_mul,Nat.add_zero,(old_drain_halt_or_emit op p a fee).1 now]
    | emit raw st => obtain ⟨_,bad,_,_⟩ := p.next_data now trace; cases bad
  | cons x rest ih =>
    have shape := (one_paid_event p.state p.valid (x::rest) trace).1
    change NextExact n (x::rest) p.pulse.result at shape
    cases now : p.pulse.result with
    | again st => exact (p.no_again now).elim
    | halt => rw [now] at shape; cases shape
    | emit raw st =>
      obtain ⟨rs,er,_,tr⟩ := p.next_data now trace
      have rr := (List.cons.inj er).2
      subst rs
      have fit : clock.val+1<2^bits := by
        rw [List.length_cons] at room
        omega
      have inc := increment_exact pos clock fit
      have fit' : (increment clock).result.val+rest.length<2^bits := by
        simp only [inc.1,List.length_cons] at room ⊢
        omega
      rw [ranked_drain_advances_one_actual_cursor_step _ _ _ _ _ now,
        (old_drain_halt_or_emit op p a _).2 now,ih _ _ _ _ tr fit']
      simp only [inc.2,List.length_cons,Nat.succ_mul]
      congr 1
      omega

#print axioms rankedDrain
#print axioms ranked_drain_halts_at_the_same_real_event
#print axioms ranked_drain_advances_one_actual_cursor_step
#print axioms old_drain_halt_or_emit
#print axioms fixed_width_traversal_adds_one_rank_increment_per_real_emission
end J6R58OrdinalSpace
