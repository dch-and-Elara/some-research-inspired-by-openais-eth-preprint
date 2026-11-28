
import J6R30ProducedGateRegistryHeterogeneous
import J6R30ProducedGateRegistryJobs

/-! Heterogeneous prepared jobs are made from the actual occurrence
header writer and the R27 compiler, not an abstract birth/envelope
oracle. Their semantic certified views do not run in the program. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R21Ancestor J6R26DescriptorTree
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {s C ell : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm key : ℕ}

def nativePackedJob {tw bw codew pagew : ℕ}
    (J : NativeJob T ticket port edge dep prec tc tz tm) (issue : Meter (J6R15ModeCost.Word key))
    (ctx : CentreContext tw bw) (shape : FrameShape f prec) (pTrue : shape.p=ticket.child.prec)
    (R : Frames shape.old shape.a shape.w codew pagew)
    (ellPos : 0<ell) (fit : shape.i.val+1≤shape.w)
    (F : OriginFields shape.a shape.p ell shape.w shape.old shape.i)
    (success : (R.compile shape.pPos ellPos fit).result=some F) :
    Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (Envelope f ell prec) where
  entry := J.job.make issue
  offset := tc+(tz+(tm+6))
  ctx := ctx
  built := packCompiled shape (R.compile shape.pPos ellPos fit)
  birth := shape.birth
  expected := ⟨shape,F⟩
  validTag := by
    have p := (source_child_precision_word J issue).1
    have matchWord : J6R15ModeCost.word ticket.child.prec=shape.birth := by
      rw [← pTrue,← shape.literal]
      exact J6R15ModeCost.valued_word _
    rw [matchWord] at p
    exact p
  validBody := by
    rw [pack_compiled_exact shape (R.compile shape.pPos ellPos fit) F success]

set_option maxHeartbeats 3200000 in
theorem actual_packed_birth {tw bw codew pagew : ℕ}
    (J : NativeJob T ticket port edge dep prec tc tz tm) (issue : Meter (J6R15ModeCost.Word key))
    (ctx : CentreContext tw bw) (shape : FrameShape f prec) (pTrue : shape.p=ticket.child.prec)
    (R : Frames shape.old shape.a shape.w codew pagew)
    (ellPos : 0<ell) (fit : shape.i.val+1≤shape.w)
    (F : OriginFields shape.a shape.p ell shape.w shape.old shape.i)
    (success : (R.compile shape.pPos ellPos fit).result=some F)
    (B : AnyLedger f ell key prec tw bw) (s : B.synced)
    (fresh : ∀ row∈B.headers,row.id≠issue.result) :
    let job := nativePackedJob J issue ctx shape pTrue R ellPos fit F success
    let pub := job.install B
    pub.result.2=true ∧ pub.result.1.synced ∧
      locate issue.result pub.result.1.records=⟨some job.immutable.payload,refHeadFee key⟩ ∧
      job.immutable.payload.payload.shape.birth=job.immutable.payload.stamp.created ∧
      job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      pub.steps=publishFee B job.entry job.offset job.built := by
  let job := nativePackedJob J issue ctx shape pTrue R ellPos fit F success
  have k : job.identifier=issue.result := J.job.make_id issue
  have ready : JobsReady B [job] := by
    refine ⟨s,by simp,?_⟩
    intro u hu row hrow
    have e := List.mem_singleton.mp hu
    rw [e,k]
    exact fresh row hrow
  have Q := (next_job_exact B job [] ready).1
  change (job.install B).result.2=true ∧ (job.install B).result.1.synced ∧
    locate issue.result (job.install B).result.1.records=⟨some job.immutable.payload,refHeadFee key⟩ ∧
    job.immutable.payload.payload.shape.birth=job.immutable.payload.stamp.created ∧
    job.immutable.payload.stamp.created.val=ticket.child.prec ∧
    (job.install B).steps=_
  rw [Q,←k]
  refine ⟨rfl,after_jobs_synced B s [job],ref_head_exact job.immutable B.records,rfl,?_,rfl⟩
  exact shape.literal.trans pTrue

#print axioms actual_packed_birth
end J6R30ProducedGateRegistry


