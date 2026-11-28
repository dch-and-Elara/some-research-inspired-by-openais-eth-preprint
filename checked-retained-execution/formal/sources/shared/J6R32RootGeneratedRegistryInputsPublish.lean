
import J6R32RootGeneratedRegistryInputsFrames
import J6R30ProducedGateRegistryPackedNative

/-! Consume the metered *actual* exterior Frames in R30's existing
publication machine. The header, body and returned reference are
the same records; their fees are not subtracted or charged twice. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R30ProducedGateRegistry J6R26DescriptorTree J6R25PreparedSupply J6R21Ancestor
open J6R24MeteredRecursion J6R15ModeCost
set_option maxHeartbeats 10000000
set_option maxRecDepth 2200

def exteriorShape {f : ℤ[X]} {p a q prec : ℕ}
    (F : Frame f p) (i : Fin a) (birth : Word prec) (truth : birth.val=p) :
    FrameShape f prec :=
  ⟨p,a,q,F.words,i,birth,truth,F.hp,F.sizePos,F.exactMod⟩

def publicationOverhead {f : ℤ[X]} {ell key prec tw bw : ℕ}
    (B : AnyLedger f ell key prec tw bw) (entry : Meter (DirRow key)) (offset : ℕ) : ℕ :=
  installFee entry B.headers+headerReadFee prec offset+locateFee key B.records.length+
    (3*key+3*prec+12)+contextCopyFee tw bw+key+14

theorem publication_fee_split {f : ℤ[X]} {ell key prec tw bw : ℕ}
    (B : AnyLedger f ell key prec tw bw) (entry : Meter (DirRow key)) (offset : ℕ)
    (body : Meter (Option (Envelope f ell prec))) :
    publishFee B entry offset body=publicationOverhead B entry offset+body.steps := by
  unfold publishFee publicationOverhead
  omega

def publishOuterFrames {f : ℤ[X]} {p ell a q codew pagew key prec tw bw : ℕ}
    (F : Frame f p) (i : Fin a) (hp : 0<ell) (fit : i.val+1≤q)
    (birth : Word prec) (truth : birth.val=p)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (B : AnyLedger f ell key prec tw bw)
    (prepared : Meter (Frames F.words a q codew pagew)) :
    Meter (AnyLedger f ell key prec tw bw×Bool) :=
  let frame := exteriorShape (q:=q) F i birth truth
  let body := packCompiled (ell:=ell) frame (Frames.compile prepared.result F.hp hp fit)
  let publish := publishCompiled B entry offset ctx body
  ⟨publish.result,prepared.steps+publish.steps+4⟩

theorem publish_outer_frames_exact {f : ℤ[X]} {p ell a q codew pagew key prec tw bw : ℕ}
    (F : Frame f p) (i : Fin a) (hp : 0<ell) (fit : i.val+1≤q)
    (birth : Word prec) (truth : birth.val=p)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (B : AnyLedger f ell key prec tw bw) (sync : B.synced)
    (fresh : ∀ row∈B.headers,row.id≠entry.result.id)
    (parsed : loadAt prec offset entry.result.bytes=⟨some birth,headerReadFee prec offset⟩)
    (prepared : Meter (Frames F.words a q codew pagew))
    (out : OriginFields a p ell q F.words i)
    (compiled : (Frames.compile prepared.result F.hp hp fit).result=some out) :
    let next := publishOuterFrames F i hp fit birth truth entry offset ctx B prepared
    let frame := exteriorShape (q:=q) F i birth truth
    let data : Envelope f ell prec := ⟨frame,out⟩
    let row := publishedRow entry.result birth ctx data
    next.result.2=true ∧ next.result.1.synced ∧ next.result.1.headers=entry.result::B.headers ∧
      next.result.1.records=row::B.records ∧
      locate entry.result.id next.result.1.records=⟨some row.payload,refHeadFee key⟩ ∧
      row.payload.stamp.created.val=p ∧
      next.steps=prepared.steps+publicationOverhead B entry offset+
        (Frames.compile prepared.result F.hp hp fit).steps+shapeFrameFee prec+4 := by
  let frame := exteriorShape (q:=q) F i birth truth
  let comp := Frames.compile prepared.result F.hp hp fit
  let data : Envelope f ell prec := ⟨frame,out⟩
  let body := packCompiled frame comp
  let row := publishedRow entry.result birth ctx data
  have J : body=⟨some data,comp.steps+shapeFrameFee prec⟩ := pack_compiled_exact frame comp out compiled
  have K := publish_compiled_exact B sync entry offset ctx body data (congrArg Meter.result J)
    birth parsed fresh
  obtain ⟨a,b,_⟩ := same_published_record entry.result birth ctx data B sync
  have fees := publication_fee_split B entry offset body
  change (publishCompiled B entry offset ctx body).result.2=true ∧
    (publishCompiled B entry offset ctx body).result.1.synced ∧
    (publishCompiled B entry offset ctx body).result.1.headers=entry.result::B.headers ∧
    (publishCompiled B entry offset ctx body).result.1.records=row::B.records ∧
    locate entry.result.id (publishCompiled B entry offset ctx body).result.1.records=
      ⟨some row.payload,refHeadFee key⟩ ∧ row.payload.stamp.created.val=p ∧ _
  rw [K]
  refine ⟨rfl,a,rfl,rfl,b,truth,?_⟩
  change prepared.steps+(publishCompiled B entry offset ctx body).steps+4=
    prepared.steps+publicationOverhead B entry offset+comp.steps+shapeFrameFee prec+4
  rw [K]
  change prepared.steps+publishFee B entry offset body+4=
    prepared.steps+publicationOverhead B entry offset+comp.steps+shapeFrameFee prec+4
  have bodyPrice : body.steps=comp.steps+shapeFrameFee prec := congrArg Meter.steps J
  rw [fees,bodyPrice]
  omega

#print axioms publication_fee_split
#print axioms publish_outer_frames_exact
end J6R32RootGeneratedRegistryInputs
