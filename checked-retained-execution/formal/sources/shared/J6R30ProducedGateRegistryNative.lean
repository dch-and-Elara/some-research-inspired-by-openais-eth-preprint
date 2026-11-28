
import J6R30ProducedGateRegistryFrames

/-! Specialization to the actual R26 child occurrence constructor.
The header passed through the raw byte bank is the one produced by
NativeJob; in particular the recorded creation word is read from
its literal native field and not copied from a later receiver. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R21Ancestor J6R26DescriptorTree
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {s C ell : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep prec tc tz tm key : ℕ}
variable (D : NativeJob T ticket port edge dep prec tc tz tm)

set_option maxHeartbeats 3200000 in
theorem native_occurrence_is_published {p a w codew pagew tw bw : ℕ}
    {old : List (A1R10.Word p)} {i : Fin a}
    (hp : 0<p) (hEll : 0<ell) (fit : i.val+1≤w) (issue : Meter (J6R15ModeCost.Word key))
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) (sync : B.synced)
    (ctx : CentreContext tw bw) (R : Frames old a w codew pagew)
    (F : OriginFields a p ell w old i) (built : (R.compile hp hEll fit).result=some F)
    (fresh : ∀ row∈B.headers,row.id≠issue.result) :
    let made := D.job.make issue
    let offset := tc+(tz+(tm+6))
    let birth := J6R15ModeCost.word (q:=prec) ticket.child.prec
    let writer := publishFrames B made offset ctx R hp hEll fit
    let row := publishedRow made.result birth ctx F
    writer.result.2=true ∧ writer.result.1.synced ∧
      row.payload.stamp.creator=issue.result ∧ row.payload.stamp.created.val=ticket.child.prec ∧
      locate issue.result writer.result.1.records=⟨some row.payload,refHeadFee key⟩ ∧
      writer.steps=publishFee B made offset (R.compile hp hEll fit) := by
  let made := D.job.make issue
  let birth := J6R15ModeCost.word (q:=prec) ticket.child.prec
  have issuer : made.result.id=issue.result := D.job.make_id issue
  obtain ⟨hTag,val⟩ := source_child_precision_word D issue
  let row := publishedRow made.result birth ctx F
  have clean : ∀ j∈B.headers,j.id≠made.result.id := by rw [issuer]; exact fresh
  have G := publish_compiled_exact B sync made (tc+(tz+(tm+6))) ctx
    (R.compile hp hEll fit) F built birth hTag clean
  have H := same_published_record made.result birth ctx F B sync
  dsimp only [publishFrames]
  rw [G]
  refine ⟨rfl,H.1,issuer,val,?_,rfl⟩
  rw [←issuer]
  exact H.2.1

#print axioms native_occurrence_is_published
end J6R30ProducedGateRegistry


