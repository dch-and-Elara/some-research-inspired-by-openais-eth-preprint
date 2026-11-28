
import J6R30ProducedGateRegistryFrames

/-! One real publish-and-read cycle. The reference bank passed to the
reader is the output of the exact same R27/R26 writer. The proof-side
payload witness is never supplied to the runtime reader. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime A1R10 J6R21Ancestor J6R20Ancestor J6R26DescriptorTree

def afterPublish {L V : Type*} (init : L) (pub : Meter (L×Bool))
    (read : L→Meter (Option V)) : Meter (L×Option V) :=
  match pub.result with
  | (next,true) =>
    let g := read next
    ⟨(next,g.result),pub.steps+g.steps+5⟩
  | (_,false) => ⟨(init,none),pub.steps+4⟩

theorem after_publish_exact {L V : Type*} (init next : L) (pub : Meter (L×Bool))
    (read : L→Meter (Option V)) (paid : ℕ) (out : Meter (Option V))
    (wrote : pub=⟨(next,true),paid⟩) (received : read next=out) :
    afterPublish init pub read=⟨(next,out.result),paid+out.steps+5⟩ := by
  unfold afterPublish
  rw [wrote]
  dsimp only
  rw [received]

def publishBuiltThenGather {p q ell a w key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (made : Meter (Option (OriginFields a p ell w old i)))
    (want : J6R15ModeCost.Word prec) (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (GateLedger (ell:=ell) (w:=w) old i key prec tw bw×Option (UVBlock new ell)) :=
  afterPublish B (publishCompiled B entry offset ctx made)
    (fun next=>gatherAndInvoke (new:=new) hp he hEll hD entry.result.id want depth wires bits next)

def publishThenGather {p q ell a w codew pagew key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (frames : Frames old a w codew pagew) (fit : i.val+1≤w)
    (want : J6R15ModeCost.Word prec) (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    Meter (GateLedger (ell:=ell) (w:=w) old i key prec tw bw×Option (UVBlock new ell)) :=
  publishBuiltThenGather (new:=new) hp he hEll hD B entry offset ctx (frames.compile hp hEll fit)
    want depth wires bits

theorem published_metered_read {p q ell a w key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (entry : DirRow key) (ctx : CentreContext tw bw) (created : J6R15ModeCost.Word prec)
    (F : OriginFields a p ell w old i) (depth : ℕ) (wires : List WireRead) (bits : List Bool) :
    let row := publishedRow entry created ctx F
    let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
      ⟨entry::B.headers,row::B.records⟩
    let g := gather (depth+a+2) wires bits
    let ev := invokeTrace (new:=new) hp he hEll hD F.probe ctx.center i ctx.codeWidth.val depth
      F.rows F.cols F.modes g.result
    gatherAndInvoke (new:=new) hp he hEll hD entry.id created depth wires bits next =
      ⟨some ev.result,g.steps+refHeadFee key+ev.steps+invokeStampFee key prec tw bw+8⟩ := by
  let row := publishedRow entry created ctx F
  let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
    ⟨entry::B.headers,row::B.records⟩
  let g := gather (depth+a+2) wires bits
  let out := invokeTrace (new:=new) hp he hEll hD F.probe ctx.center i ctx.codeWidth.val depth
    F.rows F.cols F.modes g.result
  have H : locate entry.id next.records=⟨some row.payload,refHeadFee key⟩ :=
    ref_head_exact row B.records
  have h : (locate entry.id next.records).result=some row.payload := by rw [H]
  have E := fetch_executes_record (new:=new) hp he hEll hD entry.id created depth g.result next
    row.payload h rfl rfl
  change invokeFromBank (new:=new) hp he hEll hD entry.id created depth g.result next=
    ⟨some out.result,(locate entry.id next.records).steps+out.steps+invokeStampFee key prec tw bw+4⟩ at E
  change gatherAndInvoke (new:=new) hp he hEll hD entry.id created depth wires bits next=
    ⟨some out.result,g.steps+refHeadFee key+out.steps+invokeStampFee key prec tw bw+8⟩
  unfold gatherAndInvoke
  dsimp only
  rw [E,H]
  change (⟨some out.result,g.steps+(refHeadFee key+out.steps+invokeStampFee key prec tw bw+4)+4⟩ :
    Meter (Option (UVBlock new ell)))=_
  congr 1
  omega

private theorem total_equation (p g scan exec stamp : ℕ) :
    p+(g+scan+exec+stamp+8)+5=p+g+scan+exec+stamp+13 := by omega

set_option maxHeartbeats 1700000 in
theorem compiled_cycle_exact {p q ell a w key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) (s : B.synced)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (built : Meter (Option (OriginFields a p ell w old i)))
    (created : J6R15ModeCost.Word prec)
    (readTag : loadAt prec offset entry.result.bytes=⟨some created,headerReadFee prec offset⟩)
    (fresh : ∀ row∈B.headers,row.id≠entry.result.id)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (F : OriginFields a p ell w old i) (payload : built.result=some F) :
    let row := publishedRow entry.result created ctx F
    let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
      ⟨entry.result::B.headers,row::B.records⟩
    let raw := gather (depth+a+2) wires bits
    let eval := invokeTrace (new:=new) hp he hEll hD F.probe ctx.center i ctx.codeWidth.val depth
      F.rows F.cols F.modes raw.result
    publishBuiltThenGather (new:=new) hp he hEll hD B entry offset ctx built created depth wires bits =
      ⟨(next,some eval.result),publishFee B entry offset built+raw.steps+refHeadFee key+
        eval.steps+invokeStampFee key prec tw bw+13⟩ := by
  let row := publishedRow entry.result created ctx F
  let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
    ⟨entry.result::B.headers,row::B.records⟩
  let raw := gather (depth+a+2) wires bits
  let eval := invokeTrace (new:=new) hp he hEll hD F.probe ctx.center i ctx.codeWidth.val depth
    F.rows F.cols F.modes raw.result
  have W : publishCompiled B entry offset ctx built=⟨(next,true),publishFee B entry offset built⟩ :=
    publish_compiled_exact B s entry offset ctx built F payload created readTag fresh
  have R : gatherAndInvoke (new:=new) hp he hEll hD entry.result.id created depth wires bits next =
      ⟨some eval.result,raw.steps+refHeadFee key+eval.steps+invokeStampFee key prec tw bw+8⟩ :=
    published_metered_read (new:=new) hp he hEll hD B entry.result ctx created F depth wires bits
  change publishBuiltThenGather (new:=new) hp he hEll hD B entry offset ctx built created depth wires bits =
    ⟨(next,some eval.result),publishFee B entry offset built+raw.steps+refHeadFee key+
      eval.steps+invokeStampFee key prec tw bw+13⟩
  have full := after_publish_exact B next (publishCompiled B entry offset ctx built)
    (fun V=>gatherAndInvoke (new:=new) hp he hEll hD entry.result.id created depth wires bits V)
    (publishFee B entry offset built)
    ⟨some eval.result,raw.steps+refHeadFee key+eval.steps+invokeStampFee key prec tw bw+8⟩ W R
  change afterPublish B (publishCompiled B entry offset ctx built)
    (fun V=>gatherAndInvoke (new:=new) hp he hEll hD entry.result.id created depth wires bits V)=_
  refine full.trans ?_
  exact congrArg (fun n : ℕ=> (⟨(next,some eval.result),n⟩ :
    Meter (GateLedger (ell:=ell) (w:=w) old i key prec tw bw×Option (UVBlock new ell))))
    (total_equation (publishFee B entry offset built) raw.steps (refHeadFee key) eval.steps
      (invokeStampFee key prec tw bw))

set_option maxHeartbeats 3400000 in
theorem frames_publish_and_use {p q ell a w codew pagew key prec tw bw : ℕ}
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)} {i : Fin a}
    (hp : 0<p) (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (B : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) (s : B.synced)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (frames : Frames old a w codew pagew) (fit : i.val+1≤w)
    (created : J6R15ModeCost.Word prec)
    (readTag : loadAt prec offset entry.result.bytes=⟨some created,headerReadFee prec offset⟩)
    (fresh : ∀ row∈B.headers,row.id≠entry.result.id)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool)
    (F : OriginFields a p ell w old i) (payload : (frames.compile hp hEll fit).result=some F) :
    let built := frames.compile hp hEll fit
    let row := publishedRow entry.result created ctx F
    let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
      ⟨entry.result::B.headers,row::B.records⟩
    let raw := gather (depth+a+2) wires bits
    let eval := invokeTrace (new:=new) hp he hEll hD F.probe ctx.center i ctx.codeWidth.val depth
      F.rows F.cols F.modes raw.result
    publishThenGather (new:=new) hp he hEll hD B entry offset ctx frames fit created depth wires bits =
      ⟨(next,some eval.result),publishFee B entry offset built+raw.steps+refHeadFee key+
        eval.steps+invokeStampFee key prec tw bw+13⟩ :=
  compiled_cycle_exact (new:=new) hp he hEll hD B s entry offset ctx
    (frames.compile hp hEll fit) created readTag fresh depth wires bits F payload

#print axioms after_publish_exact
#print axioms published_metered_read
#print axioms compiled_cycle_exact
#print axioms frames_publish_and_use
end J6R30ProducedGateRegistry





