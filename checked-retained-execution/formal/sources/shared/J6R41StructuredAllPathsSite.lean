import J6R36ChildFramedRouteAddons
import J6R36ChildFramedRouteForward
import J6R36ChildFramedRouteJoin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000
set_option maxRecDepth 3000

/-! A true native occurrence supplies an ordered physical parent file.
The matching addon tape is still explicit. Installation and frame
creation are the existing paid operations; no new routing service
or equality to a hypothetical emitted frame is assumed. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

structure SiteInputs (Q : Birth T v key prec tw bw page)
    (previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page) where
  ownerWidth : ℕ
  oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerWidth
  pageKey : PageAt T v→Word page
  input : List (Addon ownerWidth (dim v) key prec page)
  aligned : input=Q.native.physical.order.map (addonAt T v oldKey previous pageKey)

variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)

noncomputable abbrev SiteInputs.aux := addonAt T v S.oldKey previous S.pageKey

def SiteInputs.install : Meter (Option (List (RefRow Q.port (Addon S.ownerWidth (dim v) key prec page)))) :=
  installAddons Q.native.physical.raw S.input

def SiteInputs.bank : List (RefRow Q.port (Addon S.ownerWidth (dim v) key prec page)) :=
  S.install.result.getD []

theorem SiteInputs.install_exact :
    S.install.result=some (Q.native.physical.order.map
      (fun h=>⟨(Q.native.physical.record h).address,S.aux h⟩)) ∧
    S.install.steps=4+(S.input.map (fun x=>3*Q.port+11+
      addonFee S.ownerWidth (dim v) key prec page x.oldOrigin.pageKey.isSome)).sum :=
  prepared_addons_exact_for_same_source T v Q.native.physical S.oldKey previous S.pageKey S.input S.aligned

theorem SiteInputs.bank_exact :
    S.bank=Q.native.physical.order.map (fun h=>⟨(Q.native.physical.record h).address,S.aux h⟩) := by
  unfold SiteInputs.bank
  rw [(S.install_exact).1]
  rfl

def SiteInputs.write : Meter (FramedIssue key Q.port S.ownerWidth prec page) :=
  emitAlongsideNative Q.native Q.issuance S.bank

noncomputable def SiteInputs.frame (h : HalfAt T v) : FramedEdge Q.port S.ownerWidth key prec page :=
  frameView Q.issuance.result Q.native.receiving (Q.native.physical.record h.val) (S.aux h.val)

theorem true_site_issuance :
    S.write.result.header=Q.job.entry.result ∧ S.write.result.header.id=Q.job.identifier ∧
      S.write.result.selected=(selectPorts Q.native.gWord Q.native.physical.raw).result ∧
      S.write.result.framed=some ((halfOrder T v Q.native.physical).map S.frame) := by
  have born := framed_routes_match_the_stored_birth Q S.aux S.bank S.bank_exact
  have count := issued_frame_is_same_native_occurrence Q.native Q.issuance S.aux S.bank S.bank_exact
  exact ⟨born.1,born.2.1,count.2.2.1,born.2.2.1⟩

def SiteInputs.inWrite (x : FramedEdge Q.port S.ownerWidth key prec page) : Prop :=
  ∃ xs,S.write.result.framed=some xs ∧ x∈xs

theorem same_selected_half_written (h : HalfAt T v) : S.inWrite (S.frame h) :=
  ⟨_,(true_site_issuance S).2.2.2,List.mem_map_of_mem ((half_order_complete T v Q.native.physical).2 h)⟩

theorem full_native_creation_stamp (B : Birth T v key prec tw bw page) :
    (⟨B.issuance.result,B.native.receiving⟩ : Stamp key prec)=B.job.immutable.payload.stamp := by
  have creator : B.issuance.result=B.job.immutable.payload.stamp.creator := B.tag.1.symm
  have tag : B.native.receiving.val=B.job.immutable.payload.stamp.created.val :=
    B.native.receiveExact.trans B.tag.2.symm
  have precision : B.native.receiving=B.job.immutable.payload.stamp.created :=
    (valued_word B.native.receiving).symm.trans ((congrArg word tag).trans (valued_word _))
  exact congrArg₂ Stamp.mk creator precision

noncomputable def SiteInputs.issuedLane (h : HalfAt T v) (col : Bool) : Lane Q.port key prec page :=
  if col then (S.frame h).right else (S.frame h).left

theorem forwarding_is_same_issued_lane (h : HalfAt T v) (col : Bool) (nextGroup : Word 6) :
    (forwardRecord S.bank Q.issuance.result Q.native.receiving
      (Q.native.physical.record h.val) col nextGroup).result=some (carryLane (S.issuedLane h col) nextGroup).result := by
  have found := read_true_addon T v Q.native.physical S.aux S.bank S.bank_exact h.val
  exact (forward_bought_row S.bank Q.issuance.result Q.native.receiving
    (Q.native.physical.record h.val) (S.aux h.val) found col nextGroup).1

#print axioms SiteInputs.install_exact
#print axioms SiteInputs.bank_exact
#print axioms true_site_issuance
#print axioms same_selected_half_written
#print axioms full_native_creation_stamp
#print axioms forwarding_is_same_issued_lane
end J6R41StructuredAllPaths