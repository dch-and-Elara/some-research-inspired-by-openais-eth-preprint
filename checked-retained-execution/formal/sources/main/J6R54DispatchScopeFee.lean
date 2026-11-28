import J6R54DispatchRetained
import J6R53DispatchRawProbe

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 15500000
set_option maxRecDepth 3300
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! A live raw probe runs the exact routed LocalLoad, not an equality
premise about what it would read. The mode drain reads the actual pulse
once. The selected recipient consumes exactly the retained vector. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch J6R49DFS J6R22Active
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Slots" => ((Plan sel).Slot v.child)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

def expectedRetainedScope {Y : Type} {raw : List (Word q)} (row : RetainedTicket X raw)
    (retire : Job→ℕ)
    (go : (w : Slots)→StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Bank Y)
    (bank : Bank) : Meter (Y×Bank) :=
  let K := row.localLoad
  let next := K.result.advance.next
  let job := next.birth.job
  let child := go row.w next (afterOne bank job)
  ⟨(child.result.1,bank),row.packet.materialized.steps+6+K.result.sidecarCharge+
    (publishFee bank job.entry job.offset job.built+child.steps+retire job+4)⟩

theorem retained_scope_exact {Y : Type} {raw : List (Word q)} (row : RetainedTicket X raw)
    (retire : Job→ℕ)
    (go : (w : Slots)→StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Bank Y)
    (fallback : Meter Y) (bank : Bank)
    (good : JobsReady bank [row.localLoad.result.advance.next.birth.job]) :
    openDemand row.localLoad retire (go row.w) fallback bank=expectedRetainedScope row retire go bank :=
  accepted_event_real_scoped_step row.packet.base.geometry row.packet.base.shell row.packet.base.directory
    row.packet.materialized row.packet.checked retire (go row.w) fallback bank good

def retainedReplyWithSearch {Y B : Type*} (fee : ℕ) (s : Meter (Y×B)) : Meter Y :=
  ⟨s.result.1,fee+s.steps+4⟩

theorem raw_callback_uses_metered_retained_reply {Y : Type}
    (select : RetainedReader X q) (retire : Job→ℕ)
    (go : (w : Slots)→StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page→SM Bank Y)
    (fallback : Meter Y) (bank : Bank) (raw : List (Word q)) (g : Fin 64)
    (row : RetainedTicket X raw) (got : (select raw g).result=some row)
    (good : JobsReady bank [row.localLoad.result.advance.next.birth.job]) :
    rawCallback select retire go fallback bank raw g=
      retainedReplyWithSearch (select raw g).steps (expectedRetainedScope row retire go bank) :=
  (raw_callback_selects_exact_load select retire go fallback bank raw g row got).trans
    (congrArg (retainedReplyWithSearch (select raw g).steps)
      (retained_scope_exact row retire go fallback bank good))

def afterRetainedGroup {p width n : ℕ} (F : Frame f p)
    (op : Block F ell→List (Word width)→Meter (Block F ell))
    (read : List (Word width)→Fin 64→Meter (Block F ell))
    (now : Pending width n) (outer : Block F ell) (fee : ℕ)
    (raw : List (Word width)) (st : State width) (emitted : now.pulse.result=.emit raw st)
    (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (reply : Meter (Block F ell)) : Meter (Block F ell) :=
  let mul := mulM F.hp ⟨inner,0⟩ reply
  let product := productCursor F.hp (read raw) left mul.result (feeM+mul.steps)
  let sum := addM F.hp ⟨outer,0⟩ product
  let rest := modeDrain op (now.tail emitted) sum.result (fee+now.pulse.steps+sum.steps)
  ⟨rest.result.1,rest.steps⟩

#print axioms retained_scope_exact
#print axioms raw_callback_uses_metered_retained_reply
#print axioms afterRetainedGroup
end
end J6R54Dispatch

