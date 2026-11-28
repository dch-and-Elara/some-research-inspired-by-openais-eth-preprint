import J6R33StatefulArithmeticPageCore

/-! The real R26 issuer both writes its child bytes and fixes the
creation precision of the full per-page payload. The compiled page
table is used directly from the metered producer's returned value. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R30ProducedGateRegistry J6R26DescriptorTree

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep tc tz tm : ℕ}

def pagedJob (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw)
    (shape : FrameShape f prec) (pTrue : shape.p=ticket.child.prec)
    (built : Meter (Option (PageRows shape ell page))) (rows : PageRows shape ell page)
    (made : built.result=some rows) : PageJob f ell key prec tw bw page where
  entry := J.job.make issued
  offset := tc+(tz+(tm+6))
  ctx := ctx
  built := packPages shape built
  birth := shape.birth
  expected := ⟨shape,rows⟩
  validTag := by
    have p := (source_child_precision_word J issued).1
    have matchWord : J6R15ModeCost.word ticket.child.prec=shape.birth := by
      rw [←pTrue,←shape.literal]
      exact J6R15ModeCost.valued_word _
    rw [matchWord] at p
    exact p
  validBody := by rw [packed_pages_exact shape built rows made]

set_option maxHeartbeats 3500000 in
theorem install_full_paged_job (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issued : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw)
    (shape : FrameShape f prec) (pTrue : shape.p=ticket.child.prec)
    (built : Meter (Option (PageRows shape ell page))) (rows : PageRows shape ell page)
    (made : built.result=some rows) (B : PageBank f ell key prec tw bw page)
    (sync : B.synced) (fresh : ∀ ov∈B.headers,ov.id≠issued.result) :
    let job := pagedJob J issued ctx shape pTrue built rows made
    let out := job.install B
    out.result.2=true ∧ out.result.1.synced ∧
      job.identifier=issued.result ∧ job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      (locate issued.result out.result.1.records).result=some job.immutable.payload ∧
      job.immutable.payload.payload.pages=rows ∧
      out.steps=publishFee B job.entry job.offset ⟨some ⟨shape,rows⟩,built.steps+shapeFrameFee prec⟩ := by
  let x := pagedJob J issued ctx shape pTrue built rows made
  have tag : x.identifier=issued.result := J.job.make_id issued
  have ok : JobsReady B [x] := by
    refine ⟨sync,by simp,?_⟩
    intro j hj obj ho
    have eq := List.mem_singleton.mp hj
    exact eq ▸ tag ▸ fresh obj ho
  have e := (next_job_exact B x [] ok).1
  change (x.install B).result.2=true ∧ (x.install B).result.1.synced ∧
    x.identifier=issued.result ∧ x.immutable.payload.stamp.created.val=ticket.child.prec ∧
    (locate issued.result (x.install B).result.1.records).result=some x.immutable.payload ∧
    x.immutable.payload.payload.pages=rows ∧ (x.install B).steps=_
  rw [e]
  refine ⟨rfl,after_jobs_synced B sync [x],tag,shape.literal.trans pTrue,?_,rfl,?_⟩
  · rw [←tag]
    exact congrArg Meter.result (ref_head_exact x.immutable B.records)
  · change publishFee B x.entry x.offset (packPages shape built)=_
    rw [packed_pages_exact shape built rows made]

#print axioms install_full_paged_job
end J6R33StatefulArithmeticPage
