import J6R50SourceProducerInstaller

/-! The one-visit source artifact is published by the genuine page
registry. Payload construction is part of the publishing tariff;
the already distinct sidecar scan and retirement are not conflated. -/
namespace J6R50SourceProducer
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R41StructuredAllPaths J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R34RootAtlas J6R30ProducedGateRegistry J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 11000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "Bank" => (PageBank f ell key prec tw bw page)

/-- Creation (not retirement): the publication consumes the produced
descriptor and exactly the page rows written by its own compiler. -/
theorem produced_birth_is_published_with_actual_payload_fee
    (B : Birth T v key prec tw bw page) (registry : Bank) (sync : registry.synced)
    (fresh : ∀ x∈registry.headers,x.id≠B.issuance.result) :
    let out := B.job.install registry
    out.result.2=true ∧ out.result.1.synced ∧
      (locate B.issuance.result out.result.1.records).result=some B.job.immutable.payload ∧
      B.job.immutable.payload.payload.pages=B.rows ∧ B.compilePages.result=some B.rows ∧
      out.steps=publishFee registry B.job.entry B.job.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩ := by
  have e := install_full_paged_job B.native B.issuance B.ctx B.shape B.actualPrec
    B.compilePages B.rows B.success registry sync fresh
  exact ⟨e.1,e.2.1,e.2.2.2.2.1,e.2.2.2.2.2.1,B.success,e.2.2.2.2.2.2⟩

variable (X : StoredSite T v key prec tw bw page)
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {H : Replayed X.site w q U}
variable (W : NativeEventOnly H)

theorem actual_visit_loads_and_publishes_same_native_packet
    (D : LocalDirectory X W) (registry : Bank) (sync : registry.synced)
    (fresh : ∀ x∈registry.headers,x.id≠W.issued.result) :
    let L := prepareOnlineAdvance X W D
    let B := L.next.birth
    let installed := B.job.install registry
    installed.result.2=true ∧ installed.result.1.synced ∧
      (locate W.issued.result installed.result.1.records).result=some B.job.immutable.payload ∧
      B.job.identifier=W.issued.result ∧
      B.job.immutable.payload.stamp.created.val=(successorTicket v w).child.prec ∧
      B.job.immutable.payload.payload.pages=B.rows ∧ B.compilePages.result=some B.rows ∧
      installed.steps=publishFee registry B.job.entry B.job.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩ := by
  let L := prepareOnlineAdvance X W D
  let B := L.next.birth
  have id : B.job.identifier=W.issued.result := (occurrence_identity (localEventInput W)).1
  have tag : B.issuance.result=W.issued.result := B.tag.1.symm.trans id
  have e := produced_birth_is_published_with_actual_payload_fee B registry sync
    (fun x hx ne=>fresh x hx (ne.trans tag))
  exact ⟨e.1,e.2.1,tag ▸ e.2.2.1,id,B.tag.2,e.2.2.2.1,e.2.2.2.2.1,e.2.2.2.2.2⟩

#print axioms produced_birth_is_published_with_actual_payload_fee
#print axioms actual_visit_loads_and_publishes_same_native_packet
end
end J6R50SourceProducer