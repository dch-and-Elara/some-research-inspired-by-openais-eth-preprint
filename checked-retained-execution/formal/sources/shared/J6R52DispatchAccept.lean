import J6R52DispatchEvent
import J6R52DispatchShell
import J6R51OnlineVisitLocal

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 15500000
set_option maxRecDepth 3400
set_option linter.unusedSectionVars false

/-! Consume the actual returned Option cell of a measured dispatcher
and turn its values into the real online source LocalLoad. Shell and
directory contain no prebuilt typed event to silently select instead. -/
namespace J6R52Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R34ChildPath J6R41StructuredAllPaths
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R49SourceLayout J6R50SourceProducer J6R32StatefulArithmetic
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q} (R : Replayed X.site w q U)
local notation "nx" => (J6R48RawRoute.successorTicket v w)

structure EventGood {tc tz tm : ℕ} (e : EventBytes (q+1) tc tz tm) : Prop where
  centre : e.centre.val=centerOrdinal T nx
  probe : e.probe.val=(nx).probeAt.val
  mode : e.mode.val=modeOrdinal T nx
  group : e.group.val=(nx).groupAt.val
  exponents : e.exponents.map Word.val=liveExponentSpec R

def CheckedEvent {tc tz tm : ℕ} (m : Meter (Option (EventBytes (q+1) tc tz tm))) : Prop :=
  ∃ e,m.result=some e ∧ EventGood R e

theorem checker_returns_available {tc tz tm : ℕ}
    {m : Meter (Option (EventBytes (q+1) tc tz tm))} (g : CheckedEvent R m) : m.result.isSome :=
  Option.isSome_iff_exists.mpr (by obtain ⟨e,h,_⟩ := g; exact ⟨e,h⟩)

theorem actual_checked_bytes {tc tz tm : ℕ}
    {m : Meter (Option (EventBytes (q+1) tc tz tm))} (g : CheckedEvent R m) :
    EventGood R (m.result.get (checker_returns_available R g)) := by
  obtain ⟨e,he,h⟩ := g
  rwa [Option.get_of_eq_some _ he]

def acceptLocalLoad (B : PayloadShell R) (D : DirectorySeed R B) {tc tz tm : ℕ}
    (m : Meter (Option (EventBytes (q+1) tc tz tm))) (g : CheckedEvent R m) :
    Meter (LocalLoad X w) :=
  let e := m.result.get (checker_returns_available R g)
  let h := actual_checked_bytes R g
  ⟨loadFromShell R B D e.centre e.probe e.mode e.group
      h.centre h.probe h.mode h.group e.exponents h.exponents,m.steps+6⟩

theorem accepted_event_fee (B : PayloadShell R) (D : DirectorySeed R B) {tc tz tm : ℕ}
    (m : Meter (Option (EventBytes (q+1) tc tz tm))) (g : CheckedEvent R m) :
    let start := acceptLocalLoad R B D m g
    paidAcquisition start=m.steps+6+start.result.sidecarCharge := rfl

theorem accepted_event_loads_its_returned_data
    (B : PayloadShell R) (D : DirectorySeed R B) {tc tz tm : ℕ}
    (m : Meter (Option (EventBytes (q+1) tc tz tm))) (g : CheckedEvent R m)
    (e : EventBytes (q+1) tc tz tm) (ok : m.result=some e) :
    let K := (acceptLocalLoad R B D m g).result
    K.event.native.result.tWord=e.centre ∧ K.event.native.result.zWord=e.probe ∧
      K.event.native.result.mWord=e.mode ∧ K.event.native.result.gWord=e.group ∧
      K.event.words.result.exponents=e.exponents := by
  have h := actual_checked_bytes R g
  let z := m.result.get (checker_returns_available R g)
  have bez : z=e := Option.get_of_eq_some _ ok
  have H := shell_really_uses_input_fields R B D z.centre z.probe z.mode z.group
    h.centre h.probe h.mode h.group z.exponents h.exponents
  have ident : (acceptLocalLoad R B D m g).result.event.words.result.exponents=z.exponents := H.2.2.2.2.1
  have ta : (acceptLocalLoad R B D m g).result.event.native.result.tWord=z.centre := H.1
  have za : (acceptLocalLoad R B D m g).result.event.native.result.zWord=z.probe := H.2.1
  have ma : (acceptLocalLoad R B D m g).result.event.native.result.mWord=z.mode := H.2.2.1
  have ga : (acceptLocalLoad R B D m g).result.event.native.result.gWord=z.group := H.2.2.2.1
  rw [bez] at ident ta za ma ga
  exact ⟨ta,za,ma,ga,ident⟩

theorem accepted_event_real_scoped_step
    (B : PayloadShell R) (D : DirectorySeed R B) {tc tz tm : ℕ}
    (m : Meter (Option (EventBytes (q+1) tc tz tm))) (g : CheckedEvent R m)
    {Y : Type} (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T nx key prec tw bw page→
      J6R32StatefulArithmetic.SM (PageBank f ell key prec tw bw page) Y)
    (fallback : Meter Y) (bank : PageBank f ell key prec tw bw page)
    (ready : JobsReady bank [(acceptLocalLoad R B D m g).result.advance.next.birth.job]) :
    let K := acceptLocalLoad R B D m g
    let next := K.result.advance.next
    let job := next.birth.job
    let returned := child next (afterOne bank job)
    openDemand K retire child fallback bank=
      ⟨(returned.result.1,bank),m.steps+6+K.result.sidecarCharge+
        (publishFee bank job.entry job.offset job.built+returned.steps+retire job+4)⟩ := by
  exact open_demand_from_ready (acceptLocalLoad R B D m g) retire child fallback bank ready

#print axioms acceptLocalLoad
#print axioms accepted_event_fee
#print axioms accepted_event_loads_its_returned_data
#print axioms accepted_event_real_scoped_step
end
end J6R52Dispatch

