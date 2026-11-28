import J6R32StatefulArithmeticReadPhysical
import J6R30ProducedGateRegistryPackedNative

/-! One actual child occurrence may contain many source Pages. Keep
one occurrence header and one creation stamp; locate the independently
compiled page capsule inside that same immutable occurrence. The page
key does not replace the creator identity or birth precision. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R20Ancestor J6R24MeteredRecursion
open J6R30ProducedGateRegistry

abbrev PageRows {f : ℤ[X]} (S : FrameShape f prec) (ell page : ℕ) :=
  List (RefRow page (OriginFields S.a S.p ell S.w S.old S.i))

structure PagedEnvelope (f : ℤ[X]) (ell prec page : ℕ) where
  shape : FrameShape f prec
  pages : PageRows shape ell page

abbrev PageBank (f : ℤ[X]) (ell key prec tw bw page : ℕ) :=
  Ledger key prec tw bw (PagedEnvelope f ell prec page)

abbrev PageJob (f : ℤ[X]) (ell key prec tw bw page : ℕ) :=
  Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (PagedEnvelope f ell prec page)

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "L" => PageBank f ell key prec tw bw page
local notation "W" => Stored key prec tw bw (PagedEnvelope f ell prec page)

def packPages (S : FrameShape f prec) (built : Meter (Option (PageRows S ell page))) :
    Meter (Option (PagedEnvelope f ell prec page)) :=
  let p := J6R26DescriptorTree.duplicateWord S.birth
  let kept : FrameShape f prec := { S with
    birth := p.result
    literal := by
      change (J6R26DescriptorTree.duplicateWord S.birth).result.val=S.p
      rw [J6R26DescriptorTree.duplicate_word_exact]
      exact S.literal }
  ⟨built.result.map (fun rows=>⟨kept,rows⟩),built.steps+p.steps+13⟩

theorem packed_pages_exact (S : FrameShape f prec) (built : Meter (Option (PageRows S ell page)))
    (rows : PageRows S ell page) (h : built.result=some rows) :
    packPages S built=⟨some ⟨S,rows⟩,built.steps+shapeFrameFee prec⟩ := by
  have same : (J6R26DescriptorTree.duplicateWord S.birth).result=S.birth := by
    rw [J6R26DescriptorTree.duplicate_word_exact]
  have paid : (J6R26DescriptorTree.duplicateWord S.birth).steps=3*prec+4 := by
    rw [J6R26DescriptorTree.duplicate_word_exact]
  have K (x : J6R15ModeCost.Word prec) (hx : x.val=S.p) (hS : x=S.birth) :
      (⟨{S with birth := x, literal := hx},rows⟩ : PagedEnvelope f ell prec page)=⟨S,rows⟩ := by
    subst x
    cases S
    rfl
  have keep := K (J6R26DescriptorTree.duplicateWord S.birth).result
    (by rw [same]; exact S.literal) same
  unfold packPages
  dsimp only
  rw [h]
  simp only [Option.map_some,keep,paid,shapeFrameFee]
  congr 1

def pageFields (r : W) :=
  OriginFields r.payload.shape.a r.payload.shape.p ell r.payload.shape.w r.payload.shape.old r.payload.shape.i

def slice (r : W) (data : pageFields r) : Stored key prec tw bw (pageFields r) :=
  ⟨r.stamp,r.context,r.checkedHeader,data⟩

def onePage (r : W) (data : pageFields r) :
    Stored key prec tw bw (J6R30ProducedGateRegistry.Envelope f ell prec) :=
  ⟨r.stamp,r.context,r.checkedHeader,⟨r.payload.shape,data⟩⟩

def consumePage {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L) :
    Meter (Option (Block F ell)) :=
  let above := locate addr B.records
  match above.result with
  | none => ⟨none,above.steps+4⟩
  | some r =>
    let selected := locate pageWord r.payload.pages
    match selected.result with
    | none => ⟨none,above.steps+selected.steps+8⟩
    | some data =>
      let S := r.payload.shape
      let walked := gather (depth+S.a+2) wires bits
      let out := invokeStored S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
        addr S.birth depth walked.result (slice r data)
      ⟨out.result,above.steps+selected.steps+walked.steps+out.steps+12⟩

theorem no_page_substitution {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L)
    (r : W) (above : (locate addr B.records).result=some r)
    (missing : (locate pageWord r.payload.pages).result=none) :
    consumePage hf F hEll addr pageWord depth wires bits B=
      ⟨none,(locate addr B.records).steps+(locate pageWord r.payload.pages).steps+8⟩ := by
  unfold consumePage
  dsimp only
  rw [above]
  dsimp only
  rw [missing]

set_option maxHeartbeats 3000000 in
theorem consumes_exact_page {q : ℕ} (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (addr : J6R15ModeCost.Word key) (pageWord : J6R15ModeCost.Word page)
    (depth : ℕ) (wires : List WireRead) (bits : List Bool) (B : L)
    (r : W) (above : (locate addr B.records).result=some r)
    (data : pageFields r) (here : (locate pageWord r.payload.pages).result=some data)
    (own : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created) :
    let S := r.payload.shape
    let walk := gather (depth+S.a+2) wires bits
    let run := invokeTrace S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
      data.probe r.context.center S.i r.context.codeWidth.val depth data.rows data.cols data.modes walk.result
    consumePage hf F hEll addr pageWord depth wires bits B=
      ⟨some run.result,(locate addr B.records).steps+(locate pageWord r.payload.pages).steps+
        walk.steps+run.steps+invokeStampFee key prec tw bw+12⟩ ∧
      r.stamp.created.val=S.p := by
  let S := r.payload.shape
  let walk := gather (depth+S.a+2) wires bits
  have exec := stored_executor_exact S.pPos S.degreePos hEll (shapeCompatible S hf F.hp F.exactMod)
    addr S.birth depth walk.result (slice r data) own birth
  refine ⟨?_,birth ▸ S.literal⟩
  unfold consumePage
  dsimp only
  rw [above]
  dsimp only
  rw [here]
  dsimp only
  rw [exec]
  simp only [slice,walk,S]
  congr 1
  omega

#print axioms packed_pages_exact
#print axioms no_page_substitution
#print axioms consumes_exact_page
end J6R33StatefulArithmeticPage
