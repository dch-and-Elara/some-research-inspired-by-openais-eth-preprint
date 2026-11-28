
import J6R30ProducedGateRegistryPackedNative

/-! The native installation and consumption phases are explicitly
sequenced: the second phase gets the actual new bank returned by the
first. In particular a prepared frame's fields are not additionally
passed to the second phase, even across distinct native word shapes. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R21Ancestor J6R26DescriptorTree
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {s C ell : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm key : ℕ}

set_option maxHeartbeats 2900000 in
theorem actual_native_publication_feeds_read {tw bw codew pagew q : ℕ}
    (J : NativeJob T ticket port edge dep prec tc tz tm) (issue : Meter (J6R15ModeCost.Word key))
    (ctx : CentreContext tw bw) (shape : FrameShape f prec) (pTrue : shape.p=ticket.child.prec)
    (R : Frames shape.old shape.a shape.w codew pagew)
    (ellPos : 0<ell) (fit : shape.i.val+1≤shape.w)
    (F : OriginFields shape.a shape.p ell shape.w shape.old shape.i)
    (success : (R.compile shape.pPos ellPos fit).result=some F)
    (B : AnyLedger f ell key prec tw bw) (sync : B.synced)
    (fresh : ∀ row∈B.headers,row.id≠issue.result)
    (hq : 0<q) {new : List (A1R10.Word q)} (law : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    let job := nativePackedJob J issue ctx shape pTrue R ellPos fit F success
    let publication := job.install B
    let read := consumeEnvelope hf hq ellPos law issue.result depth wires bits publication.result.1
    let walked := gather (depth+shape.a+2) wires bits
    let eval := invokeTrace (new:=new) shape.pPos shape.degreePos ellPos
      (shapeCompatible shape hf hq law) F.probe ctx.center shape.i ctx.codeWidth.val depth
      F.rows F.cols F.modes walked.result
    publication.result.2=true ∧ publication.steps=publishFee B job.entry job.offset job.built ∧
      read=⟨some eval.result,refHeadFee key+walked.steps+eval.steps+invokeStampFee key prec tw bw+8⟩ ∧
      job.immutable.payload.stamp.created.val=ticket.child.prec := by
  let job := nativePackedJob J issue ctx shape pTrue R ellPos fit F success
  let bank := (job.install B).result.1
  let z := job.immutable.payload
  obtain ⟨ok,_,located,tag,val,price⟩ := actual_packed_birth J issue ctx shape pTrue R ellPos fit
    F success B sync fresh
  have fitLookup : locate issue.result bank.records=⟨some z,refHeadFee key⟩ := located
  have got : (locate issue.result bank.records).result=some z := by rw [fitLookup]
  have own : issue.result=z.stamp.creator := (J.job.make_id issue).symm
  have same := heterogeneous_fetched_packet hf hq ellPos law issue.result depth wires bits bank z got own tag
  refine ⟨ok,price,?_,val⟩
  have n := same.1
  change consumeEnvelope hf hq ellPos law issue.result depth wires bits bank=_
  rw [n,fitLookup]
  rfl

#print axioms actual_native_publication_feeds_read
end J6R30ProducedGateRegistry


