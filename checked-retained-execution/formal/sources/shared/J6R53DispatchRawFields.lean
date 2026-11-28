import J6R52DispatchAccept
import J6R51DispatchResidentWidths

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 13800000
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! Paste the actual emitted raw byte vector into the descendant
allocator directly, without re-running a cursor. A discovery input
selects current local shell/geometry and has a visible Meter; it is
not allowed to return a precomputed child. -/
namespace J6R53Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R51Dispatch J6R52Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R48DFS J6R50SourceProducer J6R51Online
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable (R : Replayed X.site w q U)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "d" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "t" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
local notation "A" => ((SP).levelBits v.child.depth)
local notation "Bnk" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

structure RawFields (raw : List (Word (q+1))) where
  tape : SiteTape sel d t (q+1)
  exponents : raw.map Word.val=vectorKey sel d t tape (nx).modeAt
  roster : List (RawMode (q+1))
  rosterExact : roster=tape.modes.map (encodeMode (centerIndex d t))
  tc : ℕ
  tz : ℕ
  tm : ℕ
  centre : Word tc
  probe : Word tz
  group : Word 6
  centreExact : centre.val=centerOrdinal T nx
  probeExact : probe.val=(nx).probeAt.val
  groupExact : group.val=(nx).groupAt.val
  catalogue : List (List (Word (q+1)))
  catalogueExact : catalogue=frozenCatalogueBytes T nx (residentLiteralTape d t R.certificate)
  positiveWidth : 0<tm
  catalogueFits : catalogue.length<2^tm

variable {R}

def RawFields.dispatch {raw : List (Word (q+1))} (B : RawFields R raw) :
    Meter (Option (EventBytes (q+1) B.tc B.tz B.tm)) :=
  materialize (tm:=B.tm) A B.roster R.resident.raw.roster.modes raw
    B.catalogue B.centre B.probe B.group

theorem RawFields.dispatch_checked {raw : List (Word (q+1))} (B : RawFields R raw) :
    CheckedEvent R B.dispatch ∧ B.dispatch.steps≤
      replayCap A B.roster raw R.certificate.modes.length+
      ordinalCap (q+1) B.tm R.certificate.modes.length B.catalogue.length+metadataFee B.tc B.tz := by
  obtain ⟨pages,tiles⟩ := resident_dispatch_fields_fit (centerIndex d t) R.certificate U.widthFit
  obtain ⟨E,ok,ct,zz,gg,mm,acted,fee⟩ :=
    native_materialized_event T nx B.tape R.certificate B.roster B.rosterExact raw B.exponents
      pages tiles (tm:=B.tm) B.centre B.probe B.group B.catalogue B.catalogueExact
      B.positiveWidth B.catalogueFits
  exact ⟨⟨E,ok,⟨ct.symm ▸ B.centreExact,zz.symm ▸ B.probeExact,mm,gg.symm ▸ B.groupExact,acted⟩⟩,
    fee⟩

def RawFields.load {raw : List (Word (q+1))} (B : RawFields R raw)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) : Meter (LocalLoad X w) :=
  acceptLocalLoad R shell directory B.dispatch B.dispatch_checked.1

theorem RawFields.real_scoped_step {raw : List (Word (q+1))} (B : RawFields R raw)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) {Y : Type} (retire : Job→ℕ)
    (child : StoredSite T nx key prec tw bw page → SM Bnk Y)
    (fallback : Meter Y) (bank : Bnk)
    (good : JobsReady bank [(B.load shell directory).result.advance.next.birth.job]) :
    let K := B.load shell directory
    let next := K.result.advance.next
    let job := next.birth.job
    let out := child next (afterOne bank job)
    openDemand K retire child fallback bank=
      ⟨(out.result.1,bank),B.dispatch.steps+6+K.result.sidecarCharge+
        (publishFee bank job.entry job.offset job.built+out.steps+retire job+4)⟩ :=
  accepted_event_real_scoped_step R shell directory B.dispatch B.dispatch_checked.1 retire child fallback bank good

#print axioms RawFields.dispatch
#print axioms RawFields.dispatch_checked
#print axioms RawFields.load
#print axioms RawFields.real_scoped_step
end
end J6R53Dispatch

