import J6R58OrdinalSpaceEventCore
import J6R53DispatchRawFields

/-! A table-free data carrier with genuinely paid replay and the same
checked source acceptance. The rank field must satisfy the real
native mode ordinal; it is not a supplied exponent oracle. A local
shell/directory remains a distinct acquisition input. -/
namespace J6R58OrdinalSpace
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R51Dispatch J6R52Dispatch J6R53Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R48DFS J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4100
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
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

set_option linter.unusedVariables false in
structure RankedEventFields (R : Replayed X.site w q U) (raw : List (Word (q+1))) where
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
  ordinal : Word tm
  centreExact : centre.val=centerOrdinal T nx
  probeExact : probe.val=(nx).probeAt.val
  groupExact : group.val=(nx).groupAt.val
  ordinalExact : ordinal.val=modeOrdinal T nx

variable {R} {raw : List (Word (q+1))}

def rankedDispatch (B : RankedEventFields R raw) :
    Meter (Option (EventBytes (q+1) B.tc B.tz B.tm)) :=
  materializeWithRank A B.roster R.resident.raw.roster.modes raw B.centre B.probe B.group B.ordinal

theorem real_ranked_dispatch_is_checked_and_prices_only_replay (B : RankedEventFields R raw) :
    CheckedEvent R (rankedDispatch B) ∧ (rankedDispatch B).steps≤
      replayCap A B.roster raw R.certificate.modes.length+metadataFee B.tc B.tz+(3*B.tm+1) := by
  obtain ⟨pages,tiles⟩ := resident_dispatch_fields_fit (centerIndex d t) R.certificate U.widthFit
  let addr : NativeAddress (shape SP (sourceDelta s) sel) v.child := (nx).slot.val
  obtain ⟨ready,reads,acts,fee⟩ := actual_resident_exponents_replayed d addr B.tape R.certificate
    B.roster B.rosterExact raw B.exponents pages tiles
  have formed := ordinal_event_word_and_charge_at_actual_receiver A B.roster R.resident.raw.roster.modes raw
    ready B.centre B.probe B.group B.ordinal reads
  have actual : rankedDispatch B=⟨some ⟨ready,B.centre,B.probe,B.ordinal,B.group⟩,
      (emitAndReplay A B.roster R.resident.raw.roster.modes raw).steps+metadataFee B.tc B.tz+(3*B.tm+1)⟩ := formed
  rw [actual]
  exact ⟨⟨_,rfl,⟨B.centreExact,B.probeExact,B.ordinalExact,B.groupExact,acts⟩⟩,
    Nat.add_le_add_right (Nat.add_le_add_right fee _) _⟩

def loadUsingOrdinal (B : RankedEventFields R raw) (shell : PayloadShell R)
    (directory : DirectorySeed R shell) : Meter (LocalLoad X w) :=
  acceptLocalLoad R shell directory (rankedDispatch B) (real_ranked_dispatch_is_checked_and_prices_only_replay B).1

theorem ranked_load_same_event_abi_with_no_catalogue_charge
    (B : RankedEventFields R raw) (shell : PayloadShell R) (directory : DirectorySeed R shell) :
    let K := loadUsingOrdinal B shell directory
    paidAcquisition K≤replayCap A B.roster raw R.certificate.modes.length+metadataFee B.tc B.tz+
      (3*B.tm+1)+6+K.result.sidecarCharge := by
  let law := (real_ranked_dispatch_is_checked_and_prices_only_replay B)
  have fee := accepted_event_fee R shell directory (rankedDispatch B) law.1
  dsimp only at fee ⊢
  change paidAcquisition (acceptLocalLoad R shell directory (rankedDispatch B) law.1)≤_
  rw [fee]
  exact Nat.add_le_add_right (Nat.add_le_add_right law.2 _) _

#print axioms real_ranked_dispatch_is_checked_and_prices_only_replay
#print axioms ranked_load_same_event_abi_with_no_catalogue_charge
end
end J6R58OrdinalSpace
