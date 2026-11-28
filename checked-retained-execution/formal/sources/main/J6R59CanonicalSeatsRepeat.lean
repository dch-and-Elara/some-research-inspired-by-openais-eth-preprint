import J6R59CanonicalSeatsCore

/-! Optional subsequent replay using the canonical bank, not another
scan of the offered U.rows. This operation already requires the
existing replayed seat payloads; it does not retrospectively remove
their first acquisition cost, or change R58's archived loader. -/
namespace J6R59CanonicalSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R58RequestSource J6R25PreparedSupply
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4600
set_option maxHeartbeats 22000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable (cache : CachedParentFrames X.site)
variable {u : (Plan sel).Slot v.child} {q : ℕ} {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "K" => ((q-A)+13*A)
local notation "nx" => (successorTicket v u)
local notation "i" => (axis T (successorTicket v u))
local notation "edKey" => (childKey T v X.birth.native.physical)
local notation "Order" => (childOrder X.site)
local notation "Seat" => (expectedSeat (T:=T) (v:=v) (u:=u) (q:=q))

theorem canonical_restore_same_and_bounded :
    let W := restoreSeats (canonicalBank X cache R).result (frameKeys cache.rows).result
    W.result=some R.resident.seats ∧
      W.steps≤4+v.child.edges*(locateFee X.birth.port v.child.edges+3*(A+K)+54) := by
  have bank := (canonical_bank_exact X cache R).1
  have keys := (frame_key_read_in_actual_physical_order X cache).1
  have seats := selected_payloads_are_in_the_same_physical_order X R
  dsimp only
  rw [bank,keys,seats]
  have h := restore_order_exact (Order) (Order) edKey Seat
      (child_key_injective T v X.birth.native.physical) (fun _ h=>h)
  rw [true_order_has_one_entry_per_edge X] at h
  exact h

def replayOnCanonicalBank : Meter (Option (ChildResidents A q)) :=
  let W := canonicalBank X cache R
  let replay := replayWithKeys A q (i).val U.copy U.precision U.masks W.result (some cache.rows)
  ⟨replay.result,W.steps+replay.steps+4⟩

theorem subsequent_canonical_replay_exact :
    let W := canonicalBank X cache R
    let B := frameKeys cache.rows
    let seats := restoreSeats W.result B.result
    let native := replaySelected A q (i).val U.copy U.precision U.masks R.resident.seats
    let out := replayOnCanonicalBank X cache R
    out.result=some R.resident ∧
      out.steps=W.steps+B.steps+seats.steps+native.steps+11 := by
  let keys := frameKeys cache.rows
  have wanted := (frame_key_read_in_actual_physical_order X cache).1
  have previousSeatRead :
      (restoreSeats U.rows keys.result).result=some R.resident.seats := by
    rw [show keys.result=(Order).map edKey from wanted,U.edgesExact,
      selected_payloads_are_in_the_same_physical_order X R]
    exact (restore_order_exact (Order) U.edges edKey Seat
      (child_key_injective T v X.birth.native.physical) (fun e _=>U.all e)).1
  have old := replay_cached_preserves_receipt X.site u q U cache R
  unfold replayCached replayWithKeys at old
  dsimp only at old
  rw [previousSeatRead] at old
  have canonical := (canonical_restore_same_and_bounded X cache R).1
  unfold replayOnCanonicalBank replayWithKeys
  dsimp only
  rw [canonical]
  refine ⟨old,?_⟩
  dsimp only
  omega

#print axioms canonical_restore_same_and_bounded
#print axioms replayOnCanonicalBank
#print axioms subsequent_canonical_replay_exact
end
end J6R59CanonicalSeats
