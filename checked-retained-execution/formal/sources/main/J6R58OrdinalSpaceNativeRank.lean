import J6R58OrdinalSpaceAlignment
import J6R49DFSProbe
import J6R26DescriptorTreeNative
import J6R51DispatchLegacy

/-! A conditional bridge for the literal weighted native cursor:
if its ghost transcript is the archived order, its one paid fixed
word is the very ordinal required by NativeJob and native dispatch.
No scan of the dense catalogue occurs in the implementation. -/
namespace J6R58OrdinalSpace
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS J6R51Dispatch

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3900
set_option maxHeartbeats 24000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C q bits : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable (v : Ticket sel r)
variable (I : SiteTape sel (ticketReady T v) v.centerAt q)
local notation "Order" => (((ticketActive T v).tape v.centerAt).modes)
local notation "Encode" => (vectorKey sel (ticketReady T v) v.centerAt I)

theorem live_start_at_archival_ordinal_zero (hq : 0<q)
    (compat : (Order).map Encode=tupleSpec I) :
    ∃ p : Pending q I.words.length,(startingCursor I hq).result=some p ∧
      RankAlignment Encode Order p (firstOrdinal bits).result := by
  obtain ⟨p,start,_,trace⟩ := starting_cursor_exact I hq
  refine ⟨p,start,real_first_pending_starts_at_zero_rank Encode Order p ?_⟩
  simpa only [compat] using trace

theorem literal_emitted_ordinal_is_native_job_rank
    (p : Pending q I.words.length) (i : Word bits)
    (pos : 0<bits) (width : (Order).length<2^bits)
    (align : RankAlignment Encode Order p i)
    (raw : List (Word q)) (st : State q) (emit : p.pulse.result=.emit raw st)
    (real : raw.map Word.val=Encode v.modeAt) :
    i.val=modeOrdinal T v ∧
    RankAlignment Encode Order (p.tail emit) (increment i).result := by
  classical
  obtain ⟨x,row,rank,next⟩ := actual_next_pulse_preserves_an_aligned_archival_rank
    Encode Order ((ticketActive T v).tape v.centerAt).modeUnique p i pos width align emit
  have e : x=v.modeAt := vector_key_inj sel (ticketReady T v) v.centerAt I (row.symm.trans real)
  subst x
  refine ⟨rank.trans ?_,next⟩
  unfold modeOrdinal
  apply same_index_for_lawful_comparators <;> infer_instance

#print axioms live_start_at_archival_ordinal_zero
#print axioms literal_emitted_ordinal_is_native_job_rank
end
end J6R58OrdinalSpace
