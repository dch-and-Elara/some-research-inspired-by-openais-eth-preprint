import J6R48DFSModeDrain
import J6R58OrdinalSpaceDrain

/-! The value read by the child is the word carried by the literal
cursor. An invariant licenses each call and advances with the actual
emission. Both the invariant and the admission law are proof inputs:
no complete archive, search routine, or next-rank oracle is a data
argument to the drain. -/
namespace J6R63Ordinal
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply J6R48DFS
open J6R58OrdinalSpace

set_option autoImplicit false
set_option maxRecDepth 2600
set_option maxHeartbeats 12000000

variable {q n b : ℕ} {A : Type*}
variable (Inv : Pending q n→Word b→Prop)
variable (Admit : List (Word q)→Word b→Prop)

structure EmissionLaw : Prop where
  next : ∀ (p : Pending q n) (i : Word b) (raw : List (Word q)) (st : State q)
    (e : p.pulse.result=.emit raw st), Inv p i →
      Admit raw i ∧ Inv (p.tail e) (increment i).result

def checkedDrain (law : EmissionLaw Inv Admit)
    (send : A→(raw : List (Word q))→(i : Word b)→Admit raw i→Meter A)
    (p : Pending q n) (i : Word b) (live : Inv p i) (outer : A) (bill : ℕ) :
    Meter (A×Bool) :=
  let pulse := p.pulse
  match e : pulse.result with
  | .again _ => ⟨(outer,false),bill+pulse.steps⟩
  | .halt => ⟨(outer,true),bill+pulse.steps⟩
  | .emit raw st =>
    let next := increment i
    let justified := law.next p i raw st e live
    let out := send outer raw i justified.1
    checkedDrain law send (p.tail e) next.result justified.2 out.result
      (bill+pulse.steps+next.steps+3+out.steps)
termination_by p.ghostLen
decreasing_by exact p.tail_smaller e

theorem checked_drain_halts (law : EmissionLaw Inv Admit)
    (send : A→(raw : List (Word q))→(i : Word b)→Admit raw i→Meter A)
    (p : Pending q n) (i : Word b) (live : Inv p i) (a : A) (bill : ℕ)
    (done : p.pulse.result=.halt) :
    checkedDrain Inv Admit law send p i live a bill=⟨(a,true),bill+p.pulse.steps⟩ := by
  rw [checkedDrain]
  dsimp only
  split
  · rename_i _ e
    rw [done] at e
    cases e
  · rfl
  · rename_i _ _ e
    rw [done] at e
    cases e

theorem checked_drain_sends_literal_row_and_rank_once
    (law : EmissionLaw Inv Admit)
    (send : A→(raw : List (Word q))→(i : Word b)→Admit raw i→Meter A)
    (p : Pending q n) (i : Word b) (live : Inv p i) (a : A) (bill : ℕ)
    {raw : List (Word q)} {st : State q} (e : p.pulse.result=.emit raw st) :
    let g := law.next p i raw st e live
    let out := send a raw i g.1
    checkedDrain Inv Admit law send p i live a bill=
      checkedDrain Inv Admit law send (p.tail e) (increment i).result g.2 out.result
        (bill+p.pulse.steps+(increment i).steps+3+out.steps) := by
  dsimp only
  rw [checkedDrain]
  dsimp only
  split
  · rename_i _ mismatch
    rw [e] at mismatch
    cases mismatch
  · rename_i mismatch
    rw [e] at mismatch
    cases mismatch
  · rename_i _ _ correct
    cases correct.symm.trans e
    rfl

theorem checked_drain_keeps_the_unranked_value
    (law : EmissionLaw Inv Admit)
    (send : A→(raw : List (Word q))→(i : Word b)→Admit raw i→Meter A)
    (ref : A→List (Word q)→Meter A)
    (agree : ∀ a raw i (why : Admit raw i),(send a raw i why).result=(ref a raw).result)
    (p : Pending q n) (i : Word b) (live : Inv p i) (a : A) (bill plainBill : ℕ)
    (seq : List (List ℕ)) (trace : Runs n p.state seq (.ascend [])) :
    (checkedDrain Inv Admit law send p i live a bill).result=(modeDrain ref p a plainBill).result := by
  induction seq generalizing p i a bill plainBill with
  | nil =>
    cases e : p.pulse.result with
    | again st => exact (p.no_again e).elim
    | halt =>
      rw [checked_drain_halts Inv Admit law send p i live a bill e,
        (old_drain_halt_or_emit ref p a plainBill).1 e]
    | emit raw st =>
      obtain ⟨_,broken,_,_⟩ := p.next_data e trace
      cases broken
  | cons x rest ih =>
    cases e : p.pulse.result with
    | again st => exact (p.no_again e).elim
    | halt =>
      have impossible := (one_paid_event p.state p.valid (x::rest) trace).1
      change NextExact n (x::rest) p.pulse.result at impossible
      rw [e] at impossible
      cases impossible
    | emit raw st =>
      obtain ⟨rs,found,_,more⟩ := p.next_data e trace
      have suffix := (List.cons.inj found).2
      subst rs
      have g := law.next p i raw st e live
      rw [checked_drain_sends_literal_row_and_rank_once Inv Admit law send p i live a bill e,
        (old_drain_halt_or_emit ref p a plainBill).2 e,ih (p.tail e) (increment i).result g.2 _ _ _ more]
      rw [agree]

#print axioms checkedDrain
#print axioms checked_drain_halts
#print axioms checked_drain_sends_literal_row_and_rank_once
#print axioms checked_drain_keeps_the_unranked_value
end J6R63Ordinal
