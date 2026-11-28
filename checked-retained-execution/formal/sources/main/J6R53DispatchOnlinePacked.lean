import J6R53DispatchBridge
import J6R51OnlineVisit

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 16500000
set_option maxRecDepth 3450
set_option linter.unusedSectionVars false

/-! The replacement changes only the actual demand function of the R51
runner. At a selected readAfter, the exact current offered pulse goes
through the receiving chart and the genuine scoped child transaction.
The provider supplies a live request receipt, not a completed child. -/
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

structure PackedRequest {v : Ticket sel root}
    (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child) where
  rankWidth : ℕ
  selected : ExplicitSelectedWords X.site w rankWidth
  geometry : Replayed X.site w rankWidth selected
  shell : PayloadShell geometry
  directory : DirectorySeed geometry shell
  pendingCount : ℕ
  pending : Pending (rankWidth+1) pendingCount
  catalog : List (List (Word (rankWidth+1)))
  sourceRoster : List (RawMode (rankWidth+1))
  tc : ℕ
  tz : ℕ
  tm : ℕ
  centre : Word tc
  probe : Word tz
  group : Word 6
  checked : CheckedEvent geometry
    (pulseMaterialBytes (tm:=tm) pending ((SP).levelBits v.child.depth) sourceRoster
      geometry.resident.raw.roster.modes catalog centre probe group)

def PackedRequest.meteredPulse {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : PackedRequest X w) :
    Meter (Option (EventBytes (b.rankWidth+1) b.tc b.tz b.tm)) :=
  pulseMaterialBytes (tm:=b.tm) b.pending ((SP).levelBits v.child.depth) b.sourceRoster
    b.geometry.resident.raw.roster.modes b.catalog b.centre b.probe b.group

def PackedRequest.load {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
    {w : (P).Slot v.child} (b : PackedRequest X w) : Meter (LocalLoad X w) :=
  acceptLocalLoad b.geometry b.shell b.directory b.meteredPulse b.checked

def PackedDemandSource (T : Prepared cfg sel root hf) (key prec tw bw page : ℕ) :=
  ∀ {v : Ticket sel root} (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child),
    Meter (PackedRequest X w)

def packedDemand (A : PackedDemandSource T key prec tw bw page) {v : Ticket sel root}
    (X : StoredSite T v key prec tw bw page) (w : (P).Slot v.child) : Meter (LocalLoad X w) :=
  let choose := A X w
  let current := choose.result.load
  ⟨current.result,choose.steps+current.steps+3⟩

def withPackedDispatch (M : OnlineMachine T key prec tw bw page qrun)
    (A : PackedDemandSource T key prec tw bw page) : OnlineMachine T key prec tw bw page qrun :=
  { M with demand := packedDemand A }

theorem actual_read_after_packed_pulse
    (M : OnlineMachine T key prec tw bw page qrun)
    (A : PackedDemandSource T key prec tw bw page) (retire : Job→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (active : (SP).cutoff<((P).child c u).edges) (B : Bank)
    (t : Center SP ((P).child c u)) (z : Probe SP ((P).child c u))
    (β : NativeMenu (N sel) ((P).child c u) t) (g : Fin 64)
    (ready : JobsReady B [(packedDemand A X (addressed (sel:=sel)
      (ready_reachable cfg sel (Path.step p u).reached T.rootStable active) t z β g)).result.advance.next.birth.job]) :
    let d := ready_reachable cfg sel (Path.step p u).reached T.rootStable active
    let w := addressed (sel:=sel) d t z β g
    let req := A X w
    let L := packedDemand A X w
    let n := L.result.advance.next
    let j := n.birth.job
    let out := runAfter (withPackedDispatch M A) retire ((P).child c u) (Path.step p u) w n (afterOne B j)
    readAfter (withPackedDispatch M A) retire p u X active B t z β g=
      ⟨out.result.1,req.steps+(req.result.meteredPulse.steps+6)+3+L.result.sidecarCharge+
        (publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ ∧
    out.result.2=afterOne B j := by
  exact actual_after_read_charge (withPackedDispatch M A) retire p u X active B t z β g ready

theorem packed_reader_in_actual_run
    (M : OnlineMachine T key prec tw bw page qrun)
    (A : PackedDemandSource T key prec tw bw page) (retire : Job→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel root c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (active : (SP).cutoff<((P).child c u).edges) (B : Bank) :
    let M' := withPackedDispatch M A
    let D := M'.activeAfter p u X active
    let out := D.result.eval M'.modeWidth (reachable_positive T (Path.step p u).reached)
      T.vPositive hf (readAfter M' retire p u X active B)
    runAfter M' retire c p u X B =
      (⟨(out.result,B),D.steps+out.steps⟩ : Meter (Block (T.frame (Path.step p u).reached) ell×Bank)) :=
  run_after_active_eq (withPackedDispatch M A) retire p u X active B

#print axioms PackedRequest.meteredPulse
#print axioms PackedRequest.load
#print axioms packedDemand
#print axioms withPackedDispatch
#print axioms actual_read_after_packed_pulse
#print axioms packed_reader_in_actual_run
end
end J6R53Dispatch

