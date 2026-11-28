import J6R58OrdinalSpaceNativeRank
import J6R58OrdinalSpaceNativeLoad

/-! The actual ordinal word read by a new local loader is the word
from the current literal pulse, not an independent supplied rank.
The implementation takes the already resident source roster and
already issued non-mode metadata. The order comparison is a proof
premise, not a source list passed to executable replay. -/
namespace J6R63Ordinal
open scoped Polynomial
open J6R58OrdinalSpace
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R51Dispatch J6R52Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R48DFS J6R49DFS J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3950
set_option maxHeartbeats 20500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {R : Replayed X.site w q U}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "d" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "t" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
local notation "A" => ((SP).levelBits v.child.depth)
local notation "Archive" => (((ticketActive T nx).tape t).modes)

structure FixedCoordinates (T : Prepared cfg sel root hf) (ticket : Ticket sel root) where
  tc : ℕ
  tz : ℕ
  centre : Word tc
  probe : Word tz
  group : Word 6
  centreExact : centre.val=centerOrdinal T ticket
  probeExact : probe.val=ticket.probeAt.val
  groupExact : group.val=ticket.groupAt.val

variable (I : SiteTape sel (ticketReady T (J6R48RawRoute.successorTicket v w))
  (Ticket.centerAt (J6R48RawRoute.successorTicket v w)) (q+1))
local notation "Encode" => (vectorKey sel d t I)
variable {tm : ℕ} {raw : List (Word (q+1))} {st : State (q+1)}

def fieldsAtGenuinePulse (R : Replayed X.site w q U)
    (p : Pending (q+1) I.words.length) (clock : Word tm)
    (pos : 0<tm) (room : (Archive).length<2^tm)
    (align : RankAlignment Encode Archive p clock)
    (emit : p.pulse.result=.emit raw st)
    (actual : raw.map Word.val=Encode (nx).modeAt)
    (source : List (RawMode (q+1)))
    (sourceExact : source=I.modes.map (encodeMode (centerIndex d t)))
    (coords : FixedCoordinates T nx) : RankedEventFields R raw :=
  { tape := I
    exponents := actual
    roster := source
    rosterExact := sourceExact
    tc := coords.tc
    tz := coords.tz
    tm := tm
    centre := coords.centre
    probe := coords.probe
    group := coords.group
    ordinal := clock
    centreExact := coords.centreExact
    probeExact := coords.probeExact
    groupExact := coords.groupExact
    ordinalExact := (literal_emitted_ordinal_is_native_job_rank nx I p clock pos room
      align raw st emit actual).1 }

theorem actual_pulse_supplies_same_site_checked_event
    (p : Pending (q+1) I.words.length) (clock : Word tm)
    (pos : 0<tm) (room : (Archive).length<2^tm)
    (align : RankAlignment Encode Archive p clock)
    (emit : p.pulse.result=.emit raw st)
    (actual : raw.map Word.val=Encode (nx).modeAt)
    (source : List (RawMode (q+1)))
    (sourceExact : source=I.modes.map (encodeMode (centerIndex d t)))
    (coords : FixedCoordinates T nx)
    (shell : PayloadShell R) (directory : DirectorySeed R shell) :
    let B := fieldsAtGenuinePulse I R p clock pos room align emit actual source sourceExact coords
    let K := loadUsingOrdinal B shell directory
    CheckedEvent R (rankedDispatch B) ∧ B.ordinal=clock ∧
      RankAlignment Encode Archive (p.tail emit) (increment clock).result ∧
      paidAcquisition K≤replayCap A source raw R.certificate.modes.length+metadataFee coords.tc coords.tz+
        (3*tm+1)+6+K.result.sidecarCharge := by
  let B := fieldsAtGenuinePulse I R p clock pos room align emit actual source sourceExact coords
  exact ⟨(real_ranked_dispatch_is_checked_and_prices_only_replay B).1,rfl,
    (literal_emitted_ordinal_is_native_job_rank nx I p clock pos room align raw st emit actual).2,
    ranked_load_same_event_abi_with_no_catalogue_charge B shell directory⟩

#print axioms fieldsAtGenuinePulse
#print axioms actual_pulse_supplies_same_site_checked_event
end
end J6R63Ordinal
