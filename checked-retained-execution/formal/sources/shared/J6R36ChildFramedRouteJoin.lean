import J6R36ChildFramedRouteIssue
import J6R33StatefulArithmeticPagePath

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

/-! The owner's native Birth and the structured lineage file use one
and the same actual header/issuer, not just equal local edge widths. -/
namespace J6R36ChildFramedRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C key prec tw bw page ownerW : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

theorem framed_routes_match_the_stored_birth
    (Q : Birth T v key prec tw bw page)
    (values : Port v.parent.host.Edge→Addon ownerW (dim v) key prec page)
    (bank : List (RefRow Q.port (Addon ownerW (dim v) key prec page)))
    (ready : bank=Q.native.physical.order.map (fun h=>⟨(Q.native.physical.record h).address,values h⟩)) :
    let wrapped := emitAlongsideNative Q.native Q.issuance bank
    let actual := (halfOrder T v Q.native.physical).map (fun h=>
      frameView Q.issuance.result Q.native.receiving (Q.native.physical.record h.val) (values h.val))
    wrapped.result.header=Q.job.entry.result ∧
      wrapped.result.header.id=Q.job.identifier ∧ wrapped.result.framed=some actual ∧
      (∀ row∈actual,row.right.origin.stamp.creator=Q.job.identifier ∧
        row.right.origin.stamp.created.val=Q.job.immutable.payload.stamp.created.val) := by
  have h := issued_frame_is_same_native_occurrence Q.native Q.issuance values bank ready
  refine ⟨h.1,h.2.1.trans Q.tag.1.symm,h.2.2.2.1,?_⟩
  intro row mem
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp mem
  exact ⟨Q.tag.1.symm,Q.native.receiveExact.trans Q.tag.2.symm⟩

#print axioms framed_routes_match_the_stored_birth
end J6R36ChildFramedRoute
