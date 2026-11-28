import J6R63OrdinalDispatch

/-! Exact new local fee and old checked event comparison. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R50SourceProducer J6R51Online J6R51Dispatch J6R52Dispatch J6R53Dispatch
open J6R58OrdinalSpace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3850
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child}
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "dt" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "ct" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
variable (I : SiteTape sel (ticketReady T (J6R48RawRoute.successorTicket v w))
  (Ticket.centerAt (J6R48RawRoute.successorTicket v w)) (q+1))

variable {I} {b : ℕ}
variable {raw : List (Word (q+1))} {i : Word b}

theorem actual_request_retains_current_event_and_paid_preparation
    (req : Meter (Request (X:=X) (w:=w) (q:=q) I))
    (rawExact : raw.map Word.val=vectorKey sel dt ct I (nx).modeAt)
    (rankExact : i.val=modeOrdinal T nx) :
    let A := req.result
    let B := A.current raw i rawExact rankExact
    let reply := acceptCurrent req raw i rawExact rankExact
    B.ordinal=i ∧ reply.result=(loadUsingOrdinal B A.shell A.directory).result ∧
      paidAcquisition reply=req.steps+(rankedDispatch B).steps+6+4+reply.result.sidecarCharge := by
  dsimp only
  refine ⟨rfl,rfl,?_⟩
  change req.steps+((rankedDispatch _).steps+6)+4+_=_
  omega

theorem current_request_preserves_the_legacy_local_result
    (req : Meter (Request (X:=X) (w:=w) (q:=q) I))
    (rawExact : raw.map Word.val=vectorKey sel dt ct I (nx).modeAt)
    (rankExact : i.val=modeOrdinal T nx)
    (old : Meter (Option (EventBytes (q+1) req.result.tc req.result.tz b)))
    (good : CheckedEvent req.result.replay old) :
    (acceptCurrent req raw i rawExact rankExact).result=
      (acceptLocalLoad req.result.replay req.result.shell req.result.directory old good).result := by
  let A := req.result
  let B := A.current raw i rawExact rankExact
  let work := rankedDispatch B
  change (acceptLocalLoad A.replay A.shell A.directory work
    (real_ranked_dispatch_is_checked_and_prices_only_replay B).1).result=_
  exact genuine_acceptance_depends_on_event_not_its_search_fee A.replay A.shell A.directory
    work old (real_ranked_dispatch_is_checked_and_prices_only_replay B).1 good

#print axioms actual_request_retains_current_event_and_paid_preparation
#print axioms current_request_preserves_the_legacy_local_result
end
end J6R63Ordinal
