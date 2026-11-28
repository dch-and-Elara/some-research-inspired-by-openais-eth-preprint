import J6R53DispatchBridge

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 3100
set_option linter.unusedSectionVars false

/-! Preserve the exact loaded child when forwarding already-emitted
bytes. Only the local phase meter changes, so publish/retire and the
child continuation run on exactly the same stored site. -/
namespace J6R53Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R51Dispatch J6R52Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R48DFS J6R49DFS
open J6R50SourceProducer J6R51Online
noncomputable section

theorem measured_pulse_and_forwarded_bytes {q n tc tz tm : ℕ}
    (pending : Pending q n) (raw : List (Word q)) (tail : State q)
    (emission : pending.pulse.result=.emit raw tail)
    (a : ℕ) (source receiver : List (RawMode q))
    (file : List (List (Word q))) (t : Word tc) (z : Word tz) (g : Word 6) :
    let m := materialize (tm:=tm) a source receiver raw file t z g
    pulseMaterialBytes (tm:=tm) pending a source receiver file t z g=
      ⟨m.result,pending.pulse.steps+m.steps+4⟩ := by
  unfold pulseMaterialBytes
  dsimp only
  rw [emission]

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q} {R : Replayed X.site w q U}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((SP).levelBits v.child.depth)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "Bnk" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

theorem same_accepted_value_for_same_cell (shell : PayloadShell R) (dir : DirectorySeed R shell)
    {tc tz tm : ℕ} (m n : Meter (Option (EventBytes (q+1) tc tz tm)))
    (hm : CheckedEvent R m) (hn : CheckedEvent R n) (same : m.result=n.result) :
    (acceptLocalLoad R shell dir m hm).result=(acceptLocalLoad R shell dir n hn).result := by
  cases m with
  | mk e me =>
    cases n with
    | mk j ne =>
      change e=j at same
      subst j
      rfl

theorem raw_reuse_has_identical_selected_child
    (shell : PayloadShell R) (dir : DirectorySeed R shell)
    {tc tz tm n : ℕ} (pending : Pending (q+1) n)
    (raw : List (Word (q+1))) (tail : State (q+1))
    (emitted : pending.pulse.result=.emit raw tail)
    (source : List (RawMode (q+1))) (file : List (List (Word (q+1))))
    (ct : Word tc) (zz : Word tz) (gg : Word 6)
    (h : CheckedEvent R (pulseMaterialBytes (tm:=tm) pending A source R.resident.raw.roster.modes file ct zz gg)) :
    let p := pulseMaterialBytes (tm:=tm) pending A source R.resident.raw.roster.modes file ct zz gg
    let m := materialize (tm:=tm) A source R.resident.raw.roster.modes raw file ct zz gg
    ∃ g : CheckedEvent R m,
      let K := acceptLocalLoad R shell dir p h
      let F := acceptLocalLoad R shell dir m g
      K.result=F.result ∧ K.steps=pending.pulse.steps+F.steps+4 := by
  let p := pulseMaterialBytes (tm:=tm) pending A source R.resident.raw.roster.modes file ct zz gg
  let m := materialize (tm:=tm) A source R.resident.raw.roster.modes raw file ct zz gg
  have e := measured_pulse_and_forwarded_bytes pending raw tail emitted A source
    R.resident.raw.roster.modes file ct zz gg (tm:=tm)
  let rhs : Meter (Option (EventBytes (q+1) tc tz tm)) :=
    ⟨m.result,pending.pulse.steps+m.steps+4⟩
  have eExact : p=rhs := e
  have same : p.result=m.result := show p.result=rhs.result from congrArg Meter.result eExact
  have g : CheckedEvent R m := by
    obtain ⟨x,hx,hcert⟩ := h
    exact ⟨x,same.symm.trans hx,hcert⟩
  refine ⟨g,same_accepted_value_for_same_cell shell dir p m h g same,?_⟩
  change p.steps+6 = pending.pulse.steps+(m.steps+6)+4
  have fee : p.steps=pending.pulse.steps+m.steps+4 :=
    show p.steps=rhs.steps from congrArg Meter.steps eExact
  omega

#print axioms measured_pulse_and_forwarded_bytes
#print axioms same_accepted_value_for_same_cell
#print axioms raw_reuse_has_identical_selected_child
end
end J6R53Dispatch

