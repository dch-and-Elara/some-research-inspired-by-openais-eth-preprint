import J6R33StatefulArithmeticPagePath
import J6R33PageIndexedBirthBank

/-! The child's actual metered common-file and page-request programs
are consumed directly by the actual R30 per-page compiler. Every
resident page is a separate compiled result in a single occurrence. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R30ProducedGateRegistry J6R26DescriptorTree
open J6R33PageIndexedBirth

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep tc tz tm code : ℕ}

def paidAtlas (S : FrameShape f prec)
    (raw : Meter (Common S.old S.a S.w code page))
    (requests : Meter (List (Request S.w page))) (hv : 0<ell) (fit : S.i.val+1≤S.w) :
    Meter (Option (PageRows S ell page)) :=
  let A := buildPages raw.result S.pPos hv fit requests.result
  ⟨A.result,raw.steps+requests.steps+A.steps+4⟩

theorem paid_atlas_exact {K : Type*} (S : FrameShape f prec)
    (raw : Meter (Common S.old S.a S.w code page))
    (requests : Meter (List (Request S.w page))) (hv : 0<ell) (fit : S.i.val+1≤S.w)
    (all : List K) (req : K→Request S.w page) (requestsCorrect : requests.result=all.map req)
    (field : K→OriginFields S.a S.p ell S.w S.old S.i)
    (accepted : ∀ j∈all,((raw.result.atRequest (req j)).compile S.pPos hv fit).result=some (field j)) :
    paidAtlas S raw requests hv fit=
      ⟨some (all.map fun k=>⟨(req k).key,field k⟩),
       raw.steps+requests.steps+(2+(all.map fun k=> ((raw.result.atRequest (req k)).compile S.pPos hv fit).steps+
          onePageFee page+5).sum)+4⟩ := by
  have h := build_pages_exact raw.result S.pPos hv fit all req field accepted
  unfold paidAtlas
  dsimp only
  rw [requestsCorrect,h.1,h.2]

def fromPaidAtlas {K : Type*} (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issue : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw) (S : FrameShape f prec)
    (actual : S.p=ticket.child.prec) (raw : Meter (Common S.old S.a S.w code page))
    (requests : Meter (List (Request S.w page))) (hv : 0<ell) (fit : S.i.val+1≤S.w)
    (all : List K) (uniq : all.Nodup) (req : K→Request S.w page)
    (inj : Function.Injective (fun k=>(req k).key)) (requestsCorrect : requests.result=all.map req)
    (field : K→OriginFields S.a S.p ell S.w S.old S.i)
    (accepted : ∀ j∈all,((raw.result.atRequest (req j)).compile S.pPos hv fit).result=some (field j)) :
    Birth T ticket key prec tw bw page :=
  ⟨port,edge,dep,tc,tz,tm,J,issue,ctx,S,actual,paidAtlas S raw requests hv fit,
    all.map (fun k=>⟨(req k).key,field k⟩),
    (congrArg Meter.result (paid_atlas_exact S raw requests hv fit all req requestsCorrect field accepted)),
    atlas_keys_distinct all uniq (fun k=>(req k).key) inj field⟩

set_option maxHeartbeats 5500000 in
theorem actual_atlas_is_installed_and_read {K : Type*} (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issue : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw) (S : FrameShape f prec)
    (actual : S.p=ticket.child.prec) (raw : Meter (Common S.old S.a S.w code page))
    (requests : Meter (List (Request S.w page))) (hv : 0<ell) (fit : S.i.val+1≤S.w)
    (all : List K) (uniq : all.Nodup) (req : K→Request S.w page)
    (inj : Function.Injective (fun k=>(req k).key)) (requestsCorrect : requests.result=all.map req)
    (field : K→OriginFields S.a S.p ell S.w S.old S.i)
    (accepted : ∀ j∈all,((raw.result.atRequest (req j)).compile S.pPos hv fit).result=some (field j))
    (B : PageBank f ell key prec tw bw page) (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠issue.result)
    (k : K) (legal : k∈all) :
    let born := fromPaidAtlas J issue ctx S actual raw requests hv fit all uniq req inj requestsCorrect field accepted
    let job := born.job
    let out := job.install B
    out.result.2=true ∧
      (locate issue.result out.result.1.records).result=some job.immutable.payload ∧
      (locate (req k).key job.immutable.payload.payload.pages).result=some (field k) ∧
      job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      out.steps=publishFee B job.entry job.offset ⟨some ⟨S,born.rows⟩,
        raw.steps+requests.steps+(2+(all.map fun d=>((raw.result.atRequest (req d)).compile S.pPos hv fit).steps+
          onePageFee page+5).sum)+4+shapeFrameFee prec⟩ := by
  let born := fromPaidAtlas J issue ctx S actual raw requests hv fit all uniq req inj requestsCorrect field accepted
  let job := born.job
  obtain ⟨hs,_,_,hp,hFound,_,charge⟩ :=
    install_full_paged_job born.native born.issuance born.ctx born.shape born.actualPrec
      born.compilePages born.rows born.success B sync fresh
  have H : (locate issue.result (job.install B).result.1.records).result=some job.immutable.payload := hFound
  have fee : (job.install B).steps=publishFee B job.entry job.offset
      ⟨some ⟨S,born.rows⟩, (paidAtlas S raw requests hv fit).steps+shapeFrameFee prec⟩ := charge
  rw [paid_atlas_exact S raw requests hv fit all req requestsCorrect field accepted] at fee
  exact ⟨hs,H,atlas_lookup_present all (fun j=>(req j).key) inj field k legal,hp,fee⟩

#print axioms paid_atlas_exact
#print axioms actual_atlas_is_installed_and_read
end J6R33StatefulArithmeticPage
