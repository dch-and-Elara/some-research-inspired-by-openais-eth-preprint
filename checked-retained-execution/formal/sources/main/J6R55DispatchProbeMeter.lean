import J6R53DispatchProbeValue

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

theorem same_drain_on_real_emissions (A B : V→List (Word q)→Meter V) (p : Pending q n)
    (xs : List (List ℕ)) (tr : Runs n p.state xs (.ascend []))
    (same : ∀ words : List (Word q), words.map Word.val∈xs → ∀ a,A a words=B a words)
    (a : V) (fee : ℕ) : modeDrain A p a fee=modeDrain B p a fee := by
  induction xs generalizing p a fee with
  | nil =>
    cases h : p.pulse.result with
    | again st => exact (p.no_again h).elim
    | halt => exact (drain_halt A p a fee h).trans (drain_halt B p a fee h).symm
    | emit raw st =>
      obtain ⟨rest, impossible, _, _⟩ := p.next_data h tr
      cases impossible
  | cons head rest ih =>
    cases h : p.pulse.result with
    | again st => exact (p.no_again h).elim
    | halt => exact (drain_halt A p a fee h).trans (drain_halt B p a fee h).symm
    | emit raw st =>
      obtain ⟨more,eq,_,tr'⟩ := p.next_data h tr
      obtain ⟨headEq,restEq⟩ := List.cons.inj eq
      subst head
      subst more
      rw [drain_next_is_real A p a fee h,drain_next_is_real B p a fee h,
        same raw List.mem_cons_self a]
      exact ih (p.tail h) tr'
        (fun words mem=>same words (List.mem_cons_of_mem _ mem)) _ _

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "pₜ" => registerPrecision S c t
local notation "M" => NativeMenu (shape S Δ sel) c t

/-- The entire meter (not merely its returned value) agrees whenever the
true raw reader agrees at legal decoded words. The one-pulse stream and
the group arithmetic are the same, so nothing is counted twice. -/
theorem exposed_probe_is_same_meter (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell)
    (read : List (Word q)→Fin 64→Meter (Block F ell)) (old : M→Fin 64→Meter (Block F ell))
    (same : ∀ β g,read ((vectorKey sel d t I β).map word) g=old β g) :
    probeExposed F I hq hv read=runProbe F I hq hv old := by
  obtain ⟨begin,start,_,trace⟩ := starting_cursor_exact I hq
  obtain ⟨order,_,_,orderExact⟩ := native_mode_order sel d t I
  have comp (raw : List (Word q)) (hr : raw.map Word.val∈tupleSpec I) (a : Block F ell) :
      updateExposed F hv read a raw=modeUpdate F I hv old a raw := by
    change raw.map Word.val∈strictTuples (I.modes.map modeWeight) pₜ at hr
    rw [←orderExact] at hr
    obtain ⟨β,_,hb⟩ := List.mem_map.mp hr
    have rawExact : (vectorKey sel d t I β).map word=raw :=
      (congrArg (List.map word) hb).trans (canonical_tuple_words raw)
    rw [←rawExact,mode_update_uses_actual_groups,updateExposed,funext (same β)]
  have h := same_drain_on_real_emissions (updateExposed F hv read) (modeUpdate F I hv old)
    begin (tupleSpec I) trace comp (zeroM (ell:=ell) (f:=F.words) F.hp).result
    ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps)
  rw [probeExposed,runProbe,start]
  dsimp only
  rw [h]

#print axioms same_drain_on_real_emissions
#print axioms exposed_probe_is_same_meter
end J6R55Dispatch
