import J6R53DispatchOnlinePacked
import J6R53DispatchReuse

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 16500000
set_option maxRecDepth 3450
set_option linter.unusedSectionVars false

/-! The replacement changes only the actual demand function of the R51
runner. At a selected readAfter, the caller's retained emitted raw
vector feeds the exactly same receiver and scoped child transaction.
The provider is metered, and no additional pulse is called by this loader. -/
namespace J6R53Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R16ModeCost J6R17ModeTape J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R49SourceLayout J6R50SourceProducer J6R52Dispatch J6R32StatefulArithmetic
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page qrun : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

structure ForwardedPacket {v : Ticket sel root}
    (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child) where
  base : PackedRequest X w
  raw : List (Word (base.rankWidth+1))
  tail : State (base.rankWidth+1)
  emitted : base.pending.pulse.result=.emit raw tail

def ForwardedPacket.materialized {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : ForwardedPacket X w) :
    Meter (Option (EventBytes (b.base.rankWidth+1) b.base.tc b.base.tz b.base.tm)) :=
  materialize (tm:=b.base.tm) ((SP).levelBits v.child.depth) b.base.sourceRoster
    b.base.geometry.resident.raw.roster.modes b.raw b.base.catalog b.base.centre b.base.probe b.base.group

theorem ForwardedPacket.literal_eq {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : ForwardedPacket X w) :
    b.base.meteredPulse=⟨b.materialized.result,b.base.pending.pulse.steps+b.materialized.steps+4⟩ :=
  measured_pulse_and_forwarded_bytes b.base.pending b.raw b.tail b.emitted ((SP).levelBits v.child.depth)
    b.base.sourceRoster b.base.geometry.resident.raw.roster.modes b.base.catalog b.base.centre b.base.probe b.base.group

theorem ForwardedPacket.checked {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : ForwardedPacket X w) : CheckedEvent b.base.geometry b.materialized := by
  obtain ⟨e,ok,h⟩ := b.base.checked
  have same := congrArg Meter.result b.literal_eq
  exact ⟨e,same.symm.trans ok,h⟩

def ForwardedPacket.load {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : ForwardedPacket X w) : Meter (LocalLoad X w) :=
  acceptLocalLoad b.base.geometry b.base.shell b.base.directory b.materialized b.checked

theorem ForwardedPacket.same_loaded_value {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : ForwardedPacket X w) : b.base.load.result=b.load.result := by
  have eq := congrArg Meter.result b.literal_eq
  exact same_accepted_value_for_same_cell b.base.shell b.base.directory b.base.meteredPulse
    b.materialized b.base.checked b.checked eq

def ForwardedDemandSource (T : Prepared cfg sel root hf) (key prec tw bw page : ℕ) :=
  ∀ {v : Ticket sel root} (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child),
    Meter (ForwardedPacket X w)

def forwardedDemand (A : ForwardedDemandSource T key prec tw bw page) {v : Ticket sel root}
    (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child) : Meter (LocalLoad X w) :=
  let choose := A X w
  let current := choose.result.load
  ⟨current.result,choose.steps+current.steps+3⟩

def withForwardedDispatch (M : OnlineMachine T key prec tw bw page qrun)
    (A : ForwardedDemandSource T key prec tw bw page) : OnlineMachine T key prec tw bw page qrun :=
  { M with demand := forwardedDemand A }

theorem actual_read_after_forwarded_bytes
    (M : OnlineMachine T key prec tw bw page qrun)
    (A : ForwardedDemandSource T key prec tw bw page) (retire : Job→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (active : (SP).cutoff<((P).child c u).edges) (B : Bank)
    (t : Center SP ((P).child c u)) (z : Probe SP ((P).child c u))
    (β : NativeMenu (N sel) ((P).child c u) t) (g : Fin 64)
    (ready : JobsReady B [(forwardedDemand A X (addressed (sel:=sel)
      (ready_reachable cfg sel (Path.step p u).reached T.rootStable active) t z β g)).result.advance.next.birth.job]) :
    let d := ready_reachable cfg sel (Path.step p u).reached T.rootStable active
    let w := addressed (sel:=sel) d t z β g
    let req := A X w
    let L := forwardedDemand A X w
    let n := L.result.advance.next
    let j := n.birth.job
    let out := runAfter (withForwardedDispatch M A) retire ((P).child c u) (Path.step p u) w n (afterOne B j)
    readAfter (withForwardedDispatch M A) retire p u X active B t z β g=
      ⟨out.result.1,req.steps+(req.result.materialized.steps+6)+3+L.result.sidecarCharge+
        (publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ ∧
    out.result.2=afterOne B j := by
  exact actual_after_read_charge (withForwardedDispatch M A) retire p u X active B t z β g ready

theorem forwarded_reader_in_actual_run
    (M : OnlineMachine T key prec tw bw page qrun)
    (A : ForwardedDemandSource T key prec tw bw page) (retire : Job→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (active : (SP).cutoff<((P).child c u).edges) (B : Bank) :
    let M' := withForwardedDispatch M A
    let D := M'.activeAfter p u X active
    let out := D.result.eval M'.modeWidth (reachable_positive T (Path.step p u).reached)
      T.vPositive hf (readAfter M' retire p u X active B)
    runAfter M' retire c p u X B =
      (⟨(out.result,B),D.steps+out.steps⟩ : Meter (Block (T.frame (Path.step p u).reached) ell×Bank)) :=
  run_after_active_eq (withForwardedDispatch M A) retire p u X active B

#print axioms ForwardedPacket.literal_eq
#print axioms ForwardedPacket.checked
#print axioms ForwardedPacket.same_loaded_value
#print axioms ForwardedPacket.load
#print axioms forwardedDemand
#print axioms withForwardedDispatch
#print axioms actual_read_after_forwarded_bytes
#print axioms forwarded_reader_in_actual_run
end
end J6R53Dispatch

