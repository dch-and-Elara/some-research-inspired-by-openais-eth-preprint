import J6R57PublicRequestCache
import J6R54PublicFamilyIdentity

/-! Successful recognition installs the actual native exterior
header and all-page immutable job. One shared input chart and bank
guard give readiness at all addresses; there is no per-entry mount
witness. A returned success is not a descendant execution result. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R33StatefulArithmeticPage
open J6R31RootResidentTables J6R30ProducedGateRegistry J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable (S : InstalledRequestInputs W C) (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

def cachedJobFromSource (r : Entry C.mark m native tc tj tw)
    (X : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw)
    (eq : X=(entrySource (W:=W) C r).result) :
    PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) :=
  let same := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) C r))
  let aligned := same.trans (congrArg (fun Y=>(rootPreparationFor Y).result) eq.symm)
  preparedSeed X S.root aligned pad

def cachedExteriorJob (r : Entry C.mark m native tc tj tw) :
    PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) :=
  cachedJobFromSource C S pad r (entrySource (W:=W) C r).result rfl

def admitRequest (addr : OccurrenceAddress tc tj) (raw : List Bool) :
    Meter (Option (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) × Bool)) :=
  let Q := readPublicRequest C S.requests addr raw
  match Q.result with
  | none => ⟨none,Q.steps+3⟩
  | some r =>
    let X := entrySource (W:=W) C r
    let install := (cachedJobFromSource C S pad r X.result rfl).install B
    ⟨some install.result,Q.steps+X.steps+install.steps+4⟩

theorem admission_runs_actual_selected_job
    (addr : OccurrenceAddress tc tj) (raw : List Bool) (r : Entry C.mark m native tc tj tw)
    (found : (readPublicRequest C S.requests addr raw).result=some r) :
    admitRequest C S pad B addr raw =
      ⟨some ((cachedExteriorJob C S pad r).install B).result,
        (readPublicRequest C S.requests addr raw).steps+
        (entrySource (W:=W) C r).steps+((cachedExteriorJob C S pad r).install B).steps+4⟩ := by
  unfold admitRequest
  dsimp only
  rw [found]
  rfl

theorem a_true_address_mounts_the_original_native_seed
    (sync : B.synced) (reserved : ∀ row∈B.headers,row.id.bits.take kp≠C.mark.bits)
    (addr : OccurrenceAddress tc tj) (x : Coordinate m native)
    (t : addr.centre.val=index m x.1.1) (j : addr.sample.val=x.1.2.val) (g : addr.group.val=x.2.val)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word x.1.2)) :
    let r := (emitAt W C.mark x).result
    let X := (siteFromHead W x.2 C (prepareHead W x.1.1 x.1.2).result).result
    let old := X.seed pad
    let J := cachedExteriorJob C S pad r
    let run := admitRequest C S pad B addr raw
    run.result=some (old.install B).result ∧ (old.install B).result.2=true ∧
      IsLive J (old.install B).result.1 ∧
      run.steps=(readPublicRequest C S.requests addr raw).steps+
        (ordinalFee 6 x.2.val+8)+(J.install B).steps+4 := by
  let r := (emitAt W C.mark x).result
  let X := (siteFromHead W x.2 C (prepareHead W x.1.1 x.1.2).result).result
  let old := X.seed pad
  let K := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) C r))
  let J := cachedExteriorJob C S pad r
  have id : old.identifier=X.issue.result := (stable_exterior_header X).1
  have marker : X.issue.result.bits.take kp=C.mark.bits :=
    actual_public_owner_marker W C x.1.1 x.1.2 x.2
  have fresh : ∀ row∈B.headers,row.id≠old.identifier := by
    intro row inBank h
    apply reserved row inBank
    rw [h,id,marker]
  have same : (J.install B).result=(old.install B).result :=
    (prepared_seed_exact_install X S.root K pad B sync fresh).1
  obtain ⟨ok,live⟩ := actual_public_live_from_common_bank W C x.1.1 x.1.2 x.2 pad B sync reserved
  have hit := (true_prescribed_address_is_found C S.requests addr x t j g raw legal).1
  have fee := (entry_source_is_actual (W:=W) C r).2.2.2.2
  rw [admission_runs_actual_selected_job C S pad B addr raw r hit]
  change some (J.install B).result=some (old.install B).result ∧
    (old.install B).result.2=true ∧ IsLive J (old.install B).result.1 ∧
    (readPublicRequest C S.requests addr raw).steps+(entrySource (W:=W) C r).steps+(J.install B).steps+4=_
  refine ⟨congrArg some same,ok,?_,?_⟩
  · exact (prepared_seed_same_live X S.root K pad (old.install B).result.1).mpr live
  · have coord : r.coord.2=x.2 := congrArg Prod.snd (actual_entry_wires W C.mark x).1
    have localFee : (entrySource (W:=W) C r).steps=ordinalFee 6 x.2.val+8 :=
      fee.trans (by rw [coord])
    change (readPublicRequest C S.requests addr raw).steps+
      (entrySource (W:=W) C r).steps+(J.install B).steps+4=
      (readPublicRequest C S.requests addr raw).steps+
      (ordinalFee 6 x.2.val+8)+(J.install B).steps+4
    rw [localFee]

#print axioms cachedExteriorJob
#print axioms admission_runs_actual_selected_job
#print axioms a_true_address_mounts_the_original_native_seed
end
end J6R57PublicRequest
