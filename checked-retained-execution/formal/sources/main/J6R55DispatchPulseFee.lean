import J6R55DispatchProbeMeter

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2900
set_option Elab.async false

/-! In this equality of meters, the history is purely proof-side.  No
replacement catalogue and no replay of the emitter run in either evaluator. -/
namespace J6R55Dispatch
open scoped Polynomial
open AOracleMachineTime A1R12 J6R15ModeCost J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R48DFS J6R49DFS J6R53Dispatch

variable {q n : ℕ} {V : Type*}

private theorem drain_halt (op : V→List (Word q)→Meter V) (p : Pending q n)
    (a : V) (fee : ℕ) (h : p.pulse.result=.halt) :
    modeDrain op p a fee=⟨(a,true),fee+p.pulse.steps⟩ := by
  rw [modeDrain]
  dsimp only
  split
  · rename_i st bad
    rw [h] at bad
    cases bad
  · rfl
  · rename_i raw st bad
    rw [h] at bad
    cases bad

private theorem trace_halted (p : Pending q n) (xs : List (List ℕ))
    (tr : Runs n p.state xs (.ascend [])) (h : p.pulse.result=.halt) : xs=[] := by
  have e := (one_paid_event p.state p.valid xs tr).1
  change NextExact n xs p.pulse.result at e
  rw [h] at e
  exact e

private theorem ghost_drain_halt (p : Pending q n) (h : p.pulse.result=.halt) :
    (drain p).steps=p.pulse.steps := by
  rw [drain]
  dsimp only
  split
  · rename_i st bad
    rw [h] at bad
  · rfl
  · rename_i raw st bad
    rw [h] at bad
    cases bad

private theorem ghost_drain_emit (p : Pending q n) {raw : List (Word q)} {st : State q}
    (h : p.pulse.result=.emit raw st) :
    (drain p).steps=p.pulse.steps+(drain (p.tail h)).steps := by
  rw [drain]
  dsimp only
  split
  · rename_i st bad
    rw [h] at bad
    cases bad
  · rename_i bad
    rw [h] at bad
    cases bad
  · rename_i old u actual
    have a := actual.symm.trans h
    cases a
    rfl

/-- Exact additive decomposition of the actual halt-driven meter.
`drain p` is used only as a mathematical bill for each unique next
event (including halt); it is not called by the implementation.
The operation bill accounts for what each actual cursor emission invokes. -/
theorem real_mode_drain_one_bill_per_pulse (op : V→List (Word q)→Meter V)
    (p : Pending q n) (xs : List (List ℕ))
    (tr : Runs n p.state xs (.ascend [])) (a : V) (fee : ℕ) :
    (modeDrain op p a fee).steps=fee+(drain p).steps+(foldExpected op xs a).steps := by
  induction xs generalizing p a fee with
  | nil =>
    cases h : p.pulse.result with
    | again st => exact (p.no_again h).elim
    | halt => simp only [drain_halt op p a fee h,ghost_drain_halt p h,foldExpected,Nat.add_zero]
    | emit raw st =>
      obtain ⟨rest,bad,_,_⟩ := p.next_data h tr
      cases bad
  | cons head rest ih =>
    cases h : p.pulse.result with
    | again st => exact (p.no_again h).elim
    | halt => cases trace_halted p _ tr h
    | emit raw st =>
      obtain ⟨tail,eq,_,tr'⟩ := p.next_data h tr
      obtain ⟨same,restEq⟩ := List.cons.inj eq
      subst head
      subst tail
      rw [drain_next_is_real op p a fee h,ghost_drain_emit p h,ih (p.tail h) tr']
      simp only [foldExpected,canonical_tuple_words]
      omega

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "pₜ" => registerPrecision S c t

theorem raw_probe_pays_pulses_once (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (read : List (Word q)→Fin 64→Meter (Block F ell))
    (begin : Pending q I.words.length) (ok : (startingCursor I hq).result=some begin) :
    let init := zeroM (ell:=ell) (f:=F.words) F.hp
    (probeExposed F I hq hv read).steps=init.steps+(startingCursor I hq).steps+
      (drain begin).steps+(foldExpected (updateExposed F hv read) (tupleSpec I) init.result).steps := by
  obtain ⟨B,H,_,tr⟩ := starting_cursor_exact I hq
  have eq := Option.some.inj (H.symm.trans ok)
  subst begin
  rw [probeExposed,H]
  exact real_mode_drain_one_bill_per_pulse (updateExposed F hv read) B (tupleSpec I) tr _ _

#print axioms real_mode_drain_one_bill_per_pulse
#print axioms raw_probe_pays_pulses_once
end J6R55Dispatch
