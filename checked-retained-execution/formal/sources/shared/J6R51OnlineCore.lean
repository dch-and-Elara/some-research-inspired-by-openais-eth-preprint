import J6R50SourceProducerScope
import J6R49DFSRun

/-! Demand-driven local loader and its one actual source transaction.
The result contains only the inputs for the requested slot; the
outgoing immutable job is produced inside the transaction. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6ActiveRun J6R30ProducedGateRegistry J6R48RawRoute
open J6R32StatefulArithmetic J6R48DFS J6R49DFS J6R50SourceProducer
open J6R48GeneratedAddons J6R41StructuredAllPaths
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 12500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

structure LocalLoad (X : StoredSite T v key prec tw bw page) (u : (P).Slot v.child) where
  rankWidth : ℕ
  selectedWords : ExplicitSelectedWords X.site u rankWidth
  replay : Replayed X.site u rankWidth selectedWords
  event : NativeEventOnly replay
  directory : LocalDirectory X event

def LocalLoad.advance {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} (K : LocalLoad X u) : Advance X u :=
  prepareOnlineAdvance X K.event K.directory


/-- The real local sidecar reader and installer build the already named
source bank. These two phases are not included in the R50 installation
fee of the immutable page job. -/
def LocalLoad.sidecarCharge {X : StoredSite T v key prec tw bw page}
    {u : (Plan sel).Slot v.child} (K : LocalLoad X u) : ℕ :=
  let nxt := K.advance.next
  let emitted := J6R48GeneratedAddons.emit (K.directory.read X K.event) nxt.birth.native.physical.order
  emitted.steps+nxt.site.install.steps

def paidAcquisition {X : StoredSite T v key prec tw bw page}
    {u : (Plan sel).Slot v.child} (start : Meter (LocalLoad X u)) : ℕ :=
  start.steps+start.result.sidecarCharge

/-- The caller's measured input-acquisition operation is consumed once.
The real publisher already includes the descriptor and page compiler
bill; it is not added here for a second time. -/
def openDemand {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} {R : Type}
    (started : Meter (LocalLoad X u)) (retire : J→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L R)
    (fallback : Meter R) (registry : L) : Meter (R×L) :=
  let K := started.result
  let out := visitWithActualLoad X K.event K.directory retire child fallback registry
  ⟨out.result,paidAcquisition started+out.steps⟩

theorem open_demand_exact {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} {R : Type}
    (started : Meter (LocalLoad X u)) (retire : J→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L R)
    (fallback : Meter R) (registry : L) (sync : registry.synced)
    (fresh : ∀ e∈registry.headers,e.id≠started.result.event.issued.result) :
    let next := started.result.advance.next
    let birth := next.birth
    let pushed := birth.job.install registry
    let got := child next pushed.result.1
    openDemand started retire child fallback registry =
      ⟨(got.result.1,registry),paidAcquisition started+
        (publishFee registry birth.job.entry birth.job.offset
          ⟨some ⟨birth.shape,birth.rows⟩,birth.compilePages.steps+shapeFrameFee prec⟩+
          got.steps+retire birth.job+4)⟩ := by
  have h := paid_actual_visit_is_one_scope_transaction X started.result.event started.result.directory
    retire child fallback registry sync fresh
  unfold openDemand
  dsimp only
  rw [h]
  rfl

theorem open_demand_restores {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} {R : Type}
    (started : Meter (LocalLoad X u)) (retire : J→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L R)
    (fallback : Meter R) (registry : L) :
    (openDemand started retire child fallback registry).result.2=registry :=
  paid_actual_visit_restores_parent X started.result.event started.result.directory
    retire child fallback registry

theorem loaded_job_label {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} (K : LocalLoad X u) :
    K.advance.next.birth.job.identifier=K.event.issued.result :=
  (J6R34RootAtlas.occurrence_identity (localEventInput K.event)).1

structure OnlineMachine (T : Prepared cfg sel r hf) (key prec tw bw page q : ℕ) where
  modeWidth : 0<q
  initial : (u : (P).Slot r)→Meter (StoredSite T ((Path.root : Path sel r r).ticket u) key prec tw bw page)
  demand : ∀ {v : Ticket sel r} (X : StoredSite T v key prec tw bw page) (u : (P).Slot v.child),
    Meter (LocalLoad X u)
  activeRoot : ∀ h : (S).cutoff<r.edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Path.root : Path sel r r).reached T.rootStable h) T.bank q)
  leafRoot : r.edges≤(S).cutoff→PageBank f ell key prec tw bw page→Meter (Block (T.frame (Path.root : Path sel r r).reached) ell)
  activeAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ∀ h : (S).cutoff<((P).child c u).edges,
    Meter (ActiveMachine sel (ready_reachable cfg sel (Path.step p u).reached T.rootStable h) T.bank q)
  leafAfter : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c),
    StoredSite T (p.ticket u) key prec tw bw page →
    ((P).child c u).edges≤(S).cutoff → PageBank f ell key prec tw bw page → Meter (Block (T.frame (Path.step p u).reached) ell)

variable (M : OnlineMachine T key prec tw bw page q)

/-- Specification of the same source descriptors, not an input to the
online runtime. The runtime threads the actual one stored descendant. -/
def sourceState : {c : Call (PhysicalHost f ell)} → (p : Path sel r c) → (u : (P).Slot c) →
    StoredSite T (p.ticket u) key prec tw bw page
  | _,.root,u => (M.initial u).result
  | _,.step p v,u => ((M.demand (sourceState p v) u).result.advance).next

def borns : Births T key prec tw bw page :=
  fun p u=>(sourceState M p u).birth

#print axioms LocalLoad.sidecarCharge
#print axioms open_demand_exact
#print axioms open_demand_restores
#print axioms loaded_job_label
#print axioms sourceState
end
end J6R51Online