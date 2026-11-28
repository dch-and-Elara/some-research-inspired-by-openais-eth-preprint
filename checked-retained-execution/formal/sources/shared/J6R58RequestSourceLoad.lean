import J6R58RequestSourceShell
import J6R58RequestSourceDirectory
import J6R53DispatchRawFields

/-! From a reached physical source state, build the two previously
supplied recipe parts and immediately use the original checked raw
dispatcher. The hard internal mode/address table is still an
explicit measured operand; it is not duplicated or assumed small. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas J6R20Ancestor
open J6R51ParentFrames J6R52CacheSource J6R53OldOwner
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23300000
set_option maxRecDepth 4900
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

def sourceLocalLoad : Meter (LocalLoad X u) :=
  let S := localFixedShell X R plane fitDepth fitPrec
  let D := nextDirectoryFromCurrent X cache port R gates source H inj S.result fallback
  let request := dispatchData.result.load S.result D.result
  ⟨request.result,dispatchData.steps+S.steps+D.steps+request.steps+4⟩

theorem actual_scoped_load_generated_inputs :
    let S := localFixedShell X R plane fitDepth fitPrec
    let D := nextDirectoryFromCurrent X cache port R gates source H inj S.result fallback
    let request := dispatchData.result.load S.result D.result
    let out := sourceLocalLoad X cache port R gates source H inj fallback plane fitDepth fitPrec dispatchData
    out.result=request.result ∧ out.result.event.issued=increment X.birth.job.identifier ∧
      paidAcquisition out=dispatchData.steps+S.steps+D.steps+request.steps+4+out.result.sidecarCharge := by
  exact ⟨rfl,rfl,rfl⟩

#print axioms sourceLocalLoad
#print axioms actual_scoped_load_generated_inputs
end
end J6R58RequestSource
