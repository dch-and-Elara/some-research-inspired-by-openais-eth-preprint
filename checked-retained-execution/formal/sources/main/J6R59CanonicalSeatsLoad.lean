import J6R59CanonicalSeatsDirectory
import J6R58RequestSourceLoad

/-! Run the original checked dispatcher with the canonical seat
directory. This removes the arbitrary selected-row count from the
sidecar seat lookup, not from the earlier replay or from the already
accounted legacy replay stored on the published occurrence. -/
namespace J6R59CanonicalSeats
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R53OldOwner J6R58RequestSource
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 5200
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
variable (cache : CachedParentFrames X.site) (port : PaidPortIndex X)
variable {u : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))
variable (source : CompleteRoster X.site.oldKey (parentData X gates))
variable (H : ParentOwnerHeaders X.site) (inj : Function.Injective X.site.oldKey)
variable (fallback : Addon (1+(X.site.ownerWidth+page)) (dim (successorTicket v u)) key prec page)
variable (plane : Meter (LoadedPlane X R))
variable (fitDepth : v.child.depth+1<2^X.input.dep)
variable (fitPrec : (successorTicket v u).child.prec<2^prec)
variable {raw : List (Word (q+1))}
variable (dispatchData : Meter (RawFields R raw))
local notation "Shell" => (localFixedShell X R plane fitDepth fitPrec)
local notation "Dir" => (canonicalNextDirectory X cache R (Shell).result port gates source H inj fallback)

def canonicalSourceLocalLoad : Meter (LocalLoad X u) :=
  let S := localFixedShell X R plane fitDepth fitPrec
  let D := canonicalNextDirectory X cache R S.result port gates source H inj fallback
  let request := dispatchData.result.load S.result D.result
  ⟨request.result,dispatchData.steps+S.steps+D.steps+request.steps+4⟩

local notation "Out" => (canonicalSourceLocalLoad X cache port R gates source H inj fallback plane fitDepth fitPrec dispatchData)

theorem real_loader_uses_canonical_seat_count :
    (Out).result.directory.seats.length=v.child.edges := by
  change (canonicalDirectorySeats X cache R (Shell).result).result.length=_
  exact (physical_table_count_distinct_and_bits X cache R (Shell).result).1

theorem canonical_loader_keeps_dispatch_and_charges_exactly :
    let old := sourceLocalLoad X cache port R gates source H inj fallback plane fitDepth fitPrec dispatchData
    let out := Out
    out.result.event=old.result.event ∧
      out.result.event.issued=increment X.birth.job.identifier ∧
      paidAcquisition out=dispatchData.steps+(Shell).steps+(Dir).steps+
        (dispatchData.result.load (Shell).result (Dir).result).steps+4+out.result.sidecarCharge ∧
      (localEventWords out.result.event).physical.steps=(replayChild X.site u q U).steps :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem local_loader_actual_seat_read_uses_edge_count (h : Port v.child.host.Edge) :
    let out := Out
    let D := out.result.directory
    (D.read X out.result.event h).steps ≤ (D.queries h).steps+locateFee D.k1 D.owners.length+
      locateFee X.birth.port v.child.edges+10 := by
  have bound := actual_sidecar_lookup_bound_uses_physical_edges X cache R (Shell).result port gates source H inj h
  change (residentRead (buildOriginBank X gates source H inj).result
    (canonicalDirectorySeats X cache R (Shell).result).result (queryActualPort X cache port h)).steps+2 ≤ _
  change (residentRead (buildOriginBank X gates source H inj).result
    (canonicalDirectorySeats X cache R (Shell).result).result (queryActualPort X cache port h)).steps+2 ≤
      (queryActualPort X cache port h).steps+
      locateFee (1+(X.site.ownerWidth+page)) (buildOriginBank X gates source H inj).result.length+
      locateFee X.birth.port v.child.edges+10
  omega

#print axioms canonicalSourceLocalLoad
#print axioms real_loader_uses_canonical_seat_count
#print axioms canonical_loader_keeps_dispatch_and_charges_exactly
#print axioms local_loader_actual_seat_read_uses_edge_count
end
end J6R59CanonicalSeats
