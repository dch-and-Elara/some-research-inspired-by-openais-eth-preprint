import J6R41StructuredAllPathsSite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11500000
set_option maxRecDepth 3100

/-! Each real child endpoint uses the very row framed beside the actual
R26 header. A new Page has no predecessor body premise. A retained
endpoint only needs the body of its own previous port, not a proposed
body at the current vertex. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R20Ancestor

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)

noncomputable def nativeOrigin (k : PageAt T v) : Origin key prec page :=
  ⟨Q.job.immutable.payload.stamp,some (S.pageKey k)⟩

theorem native_page_body_at_issue (k : PageAt T v) (x : PortAt (bornPoint T v k))
    (nextGroup : Word 6) :
    let h := edge x.val
    let lane := S.issuedLane h true
    S.inWrite (S.frame h) ∧
      lane.body=originSeed (layout T v) (axis T v) v.groupAt k x ∧
      lane.origin=nativeOrigin S k ∧ lane.origin.stamp.created.val=(entry (bornPoint T v k)).created := by
  let h := edge x.val
  let lane := S.issuedLane h true
  have step := actual_fresh_route_start T v Q.native Q.issuance S.oldKey previous S.pageKey
    S.bank S.bank_exact k x nextGroup
  have eq := (forwarding_is_same_issued_lane S h true nextGroup).symm.trans step.1
  change some (carryLane lane nextGroup).result=_ at eq
  rw [carry_keeps_body_and_stamp] at eq
  have same := Option.some.inj eq
  have b := congrArg (fun v : PortRow (Q.port+1)×Origin key prec page=>v.1.body) same
  have o := congrArg (fun v : PortRow (Q.port+1)×Origin key prec page=>v.2) same
  have stamp : lane.origin=nativeOrigin S k := o.trans (congrArg (fun s=>Origin.mk s (some (S.pageKey k)))
    (full_native_creation_stamp Q))
  refine ⟨same_selected_half_written S h,b,stamp,?_⟩
  change lane.origin.stamp.created.val=(entry (bornPoint T v k)).created
  exact (congrArg (fun a : Origin key prec page=>a.stamp.created.val) o).trans step.2

theorem native_retained_body_at_issue (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val)) (seed : PortAt root→List Bool)
    (x : PortAt (retainedMove T v u).next) (nextGroup : Word 6)
    (parentBody : (Q.native.physical.record ((retainedMove T v u).back x).val).body=
      tr.literal seed ((retainedMove T v u).back x)) :
    let h := edge x.val
    let lane := S.issuedLane h false
    S.inWrite (S.frame h) ∧
      lane.body=(tr.keep (retainedMove T v u)).literal seed x ∧ lane.origin=previous u.val := by
  let h := edge x.val
  let lane := S.issuedLane h false
  have cell := (retainedMove T v u).back_val x
  have step := actual_retained_route_step T v Q.native Q.issuance S.oldKey previous
    S.pageKey S.bank S.bank_exact u tr seed x nextGroup parentBody
  change (forwardRecord S.bank Q.issuance.result Q.native.receiving
    (Q.native.physical.record ((retainedMove T v u).back x).val) false nextGroup).result=some _ at step
  rw [cell] at step
  have eq := (forwarding_is_same_issued_lane S h false nextGroup).symm.trans step
  change some (carryLane lane nextGroup).result=_ at eq
  rw [carry_keeps_body_and_stamp] at eq
  have same := Option.some.inj eq
  exact ⟨same_selected_half_written S h,
    congrArg (fun v : PortRow (Q.port+1)×Origin key prec page=>v.1.body) same,
    congrArg (fun v : PortRow (Q.port+1)×Origin key prec page=>v.2) same⟩

#print axioms native_page_body_at_issue
#print axioms native_retained_body_at_issue
end J6R41StructuredAllPaths