import J6R50SourceProducerKeyed

/-! The actual frame producer over indexed addon rows already paid
elsewhere. Neither branch rewrites the native publication header. -/
namespace J6R51ParentFrames
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage
open J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2700
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)

abbrev AddonRows := List (RefRow Q.port (Addon S.ownerWidth (dim v) key prec page))

abbrev FrameRows := List (FramedEdge Q.port S.ownerWidth key prec page)

/-- Mount only the actual selected frames; the selected rows and the
indexed addon rows are both already available to the caller. -/
def framesFromSelected (bank : AddonRows S) (selected : List (PortRow Q.port)) :
    Meter (Option (FrameRows S)) :=
  frameBatch bank Q.issuance.result Q.native.receiving selected

/-- If the selected port list was not retained by the paid header
producer, do one explicit selection scan, but do not reconstruct its
native header, depth, issuance word or copy of the descriptor bytes. -/
def paidParentFrames (bank : AddonRows S) : Meter (Option (FrameRows S)) :=
  selectedFrame Q.native.gWord Q.native.physical.raw bank Q.issuance.result Q.native.receiving

theorem shared_parent_frames_exact (bank : AddonRows S) (bankEQ : bank=S.bank)
    (selected : List (PortRow Q.port)) (selectedEQ : selected=S.write.result.selected) :
    (framesFromSelected S bank selected).result=S.write.result.framed ∧
      S.write.steps=Q.job.entry.steps+(framesFromSelected S bank selected).steps+7 := by
  subst bank
  subst selected
  have e := issued_frame_is_same_native_occurrence Q.native Q.issuance S.aux S.bank S.bank_exact
  exact ⟨rfl,e.2.2.2.2⟩

theorem paid_parent_frames_exact (bank : AddonRows S) (bankEQ : bank=S.bank) :
    let selected := selectPorts Q.native.gWord Q.native.physical.raw
    (paidParentFrames S bank).result=S.write.result.framed ∧
      (paidParentFrames S bank).steps=selected.steps+(framesFromSelected S bank selected.result).steps+5 := by
  have e := (true_site_issuance S).2.2.1
  exact ⟨(shared_parent_frames_exact S bank bankEQ _ e.symm).1,rfl⟩

theorem paid_parent_frames_are_the_actual_order (bank : AddonRows S) (bankEQ : bank=S.bank) :
    (paidParentFrames S bank).result=some ((halfOrder T v Q.native.physical).map S.frame) :=
  (paid_parent_frames_exact S bank bankEQ).1.trans (true_site_issuance S).2.2.2

theorem paid_parent_frames_local_cap (bank : AddonRows S) (bankEQ : bank=S.bank) :
    (paidParentFrames S bank).steps≤11+(Q.native.physical.raw.map rowScanFee).sum+
      ((halfOrder T v Q.native.physical).map (fun h=>visitFee Q.port S.ownerWidth (dim v) key prec page
        bank.length (Q.native.physical.record h.val).body.length (S.aux h.val).oldOrigin.pageKey.isSome)).sum := by
  have b : bank=Q.native.physical.order.map
      (fun h=>⟨(Q.native.physical.record h).address,S.aux h⟩) := bankEQ.trans S.bank_exact
  exact (native_frames_from_actual_selection T v Q.native Q.issuance S.aux bank b).2

#print axioms shared_parent_frames_exact
#print axioms paid_parent_frames_exact
#print axioms paid_parent_frames_are_the_actual_order
#print axioms paid_parent_frames_local_cap
end J6R51ParentFrames
