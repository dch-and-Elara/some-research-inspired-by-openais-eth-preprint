import J6R58RequestSourceLoad

namespace J6R59Public
open scoped Polynomial Classical
open J6R58RequestSource
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
set_option maxHeartbeats 5700000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
theorem owner_projection_does_not_determine_gate_code
    {width gate key prec page : ℕ}
    (left right : RefRow width (OwnerData gate key prec page))
    (address : left.address=right.address)
    (origin : left.payload.origin=right.payload.origin)
    (different : left.payload.gateCode≠right.payload.gateCode) :
    writeOriginRow left=writeOriginRow right ∧ left≠right := by
  refine ⟨?_,fun e=>different (congrArg (fun row=>row.payload.gateCode) e)⟩
  unfold writeOriginRow
  rw [address,origin]

section Step
variable {f : ℤ[X]} {ell s C key prec tw bw page gwidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (Y : StoredSite T v key prec tw bw page)
variable {u : (Plan sel).Slot v.child}
variable (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word gwidth)))

structure HeldOwnerLoad where
  load : LocalLoad Y u
  held : CompleteRoster (nameCurrentOwner Y) (childData Y gates)

section Builder
variable (cache : CachedParentFrames Y.site) (port : PaidPortIndex Y)
variable {q : ℕ} {U : ExplicitSelectedWords Y.site u q}
variable (R : Replayed Y.site u q U)
variable (source : CompleteRoster Y.site.oldKey (parentData Y gates))
variable (H : ParentOwnerHeaders Y.site) (inj : Function.Injective Y.site.oldKey)
variable (fallback : Addon (1+(Y.site.ownerWidth+page)) (dim (successorTicket v u)) key prec page)
variable (plane : Meter (LoadedPlane Y R))
variable (fitDepth : v.child.depth+1<2^Y.input.dep)
variable (fitPrec : (successorTicket v u).child.prec<2^prec)
variable {raw : List (Word (q+1))}
variable (dispatchData : Meter (RawFields R raw))

/-- Keep the full physical roster evaluated by the R58 directory writer.
The erased proof coercion only identifies its gate history with the new
site's. No second roster writer or install occurs in this constructor. -/
def keepR58OwnerLoad : Meter (HeldOwnerLoad Y (u:=u) gates) :=
  let copies := openCurrentOwners Y gates source H inj
  let origins := J6R57PublicRequest.emitRows writeOriginRow copies.result.raw
  let sh := localFixedShell Y R plane fitDepth fitPrec
  let dir : DirectorySeed R sh.result :=
    ⟨1+(Y.site.ownerWidth+page),Y.birth.port,1+(Y.site.ownerWidth+page),nameCurrentOwner Y,origins.result,
      directorySeatRows R sh.result,queryActualPort Y cache port,fallback,
      generated_native_routes_all_hit Y cache port R gates source H inj sh.result⟩
  let op := dispatchData.result.load sh.result dir
  ⟨⟨op.result,copies.result⟩,
    dispatchData.steps+sh.steps+((copies.steps+origins.steps+4)+4)+op.steps+4⟩

theorem held_loader_projects_to_the_actual_R58_meter :
    let k := keepR58OwnerLoad Y gates cache port R source H inj fallback plane fitDepth fitPrec dispatchData
    (⟨k.result.load,k.steps⟩ : Meter (LocalLoad Y u))=
      sourceLocalLoad Y cache port R gates source H inj fallback plane fitDepth fitPrec dispatchData := rfl
end Builder

end Step
#print axioms owner_projection_does_not_determine_gate_code
#print axioms keepR58OwnerLoad
#print axioms held_loader_projects_to_the_actual_R58_meter
end
end J6R59Public
