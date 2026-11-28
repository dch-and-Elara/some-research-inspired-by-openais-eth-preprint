import J6R34RootAtlasWiden
import J6R34RootAtlasHeader
import J6R33StatefulArithmeticPageInitial

/-! Fit a root atlas into the chosen common tree width and install its
actual payload. The raw header's checked birth persists; exact lookup
resolves the physically widened Page without modifying its Gate. -/
namespace J6R34RootAtlas
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R26DescriptorTree J6R32StatefulArithmetic

def widenAtlas {n : ℕ} {D : Type*} (ext : ℕ) (xs : Meter (Option (List (RefRow n D)))) :
    Meter (Option (List (RefRow (n+ext) D))) :=
  match xs.result with
  | none => ⟨none,xs.steps+4⟩
  | some rows =>
    let out := widenRows ext rows
    ⟨some out.result,xs.steps+out.steps+4⟩

theorem widen_atlas_exact {n : ℕ} {D : Type*} (ext : ℕ) (xs : Meter (Option (List (RefRow n D))))
    (rows : List (RefRow n D)) (h : xs.result=some rows) :
    widenAtlas ext xs=⟨some (rows.map (mappedRow ext)),xs.steps+(2+rows.length*(wideningFee n ext+7))+4⟩ := by
  rw [widenAtlas,h]
  dsimp only
  rw [widened_rows_exact]

variable {f : ℤ[X]} {ell key prec tw bw n : ℕ}

def rootJob (S : FrameShape f prec) (E : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (tag : loadAt prec offset E.result.bytes=⟨some S.birth,headerReadFee prec offset⟩)
    (ext : ℕ) (build : Meter (Option (PageRows S ell n))) (rows : PageRows S ell n)
    (ok : build.result=some rows) : PageJob f ell key prec tw bw (n+ext) where
  entry := E
  offset := offset
  ctx := ctx
  built := packPages S (widenAtlas ext build)
  birth := S.birth
  expected := ⟨S,rows.map (mappedRow ext)⟩
  validTag := tag
  validBody := by
    rw [packed_pages_exact S (widenAtlas ext build) _ (congrArg Meter.result (widen_atlas_exact ext build rows ok))]

set_option maxHeartbeats 5600000 in
theorem actual_root_seed_paid (S : FrameShape f prec) (E : Meter (DirRow key))
    (offset : ℕ) (ctx : CentreContext tw bw)
    (tag : loadAt prec offset E.result.bytes=⟨some S.birth,headerReadFee prec offset⟩)
    (ext : ℕ) (build : Meter (Option (PageRows S ell n))) (rows : PageRows S ell n)
    (ok : build.result=some rows) (B : PageBank f ell key prec tw bw (n+ext))
    (sync : B.synced) (fresh : ∀ r∈B.headers,r.id≠E.result.id)
    (page : J6R15ModeCost.Word n) (data : OriginFields S.a S.p ell S.w S.old S.i)
    (actual : (locate page rows).result=some data) :
    let j := rootJob S E offset ctx tag ext build rows ok
    let out := j.install B
    out.result.2=true ∧ IsLive j out.result.1 ∧
      (locate (widened ext page).result j.immutable.payload.payload.pages).result=some data ∧
      j.immutable.payload.stamp.created.val=S.p ∧
      out.steps=publishFee B E offset
        ⟨some ⟨S,rows.map (mappedRow ext)⟩,
          build.steps+(2+rows.length*(wideningFee n ext+7))+4+shapeFrameFee prec⟩ := by
  let j := rootJob S E offset ctx tag ext build rows ok
  have h : JobsReady B [j] := by
    refine ⟨sync,by simp,?_⟩
    intro d hd r hm
    obtain rfl := List.mem_singleton.mp hd
    exact fresh r hm
  have pub := (next_job_exact B j [] h).1
  have w := widened_lookup_same ext rows page
  rw [widened_rows_exact ext rows, actual] at w
  change (j.install B).result.2=true ∧ IsLive j (j.install B).result.1 ∧
    (locate (widened ext page).result j.immutable.payload.payload.pages).result=some data ∧
    j.immutable.payload.stamp.created.val=S.p ∧ (j.install B).steps=_
  rw [pub]
  refine ⟨rfl,new_is_live j B,w,S.literal,?_⟩
  change publishFee B E offset (packPages S (widenAtlas ext build))=_
  rw [packed_pages_exact S (widenAtlas ext build) _ (congrArg Meter.result (widen_atlas_exact ext build rows ok)),
    widen_atlas_exact ext build rows ok]

#print axioms widen_atlas_exact
#print axioms actual_root_seed_paid
end J6R34RootAtlas
