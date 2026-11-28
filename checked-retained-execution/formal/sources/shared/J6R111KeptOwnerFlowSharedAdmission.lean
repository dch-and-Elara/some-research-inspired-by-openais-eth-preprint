import J6R57PublicRequestLive
import J6R55PublicReserve

/-! R57's one real request/entry/install path, retaining the physical
site it just produced. The acknowledgement and the metered entry both
come from this operation, so later code need not emit a second site. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R33StatefulArithmeticPage J6R57PublicRequest
open J6R31RootResidentTables J6R30ProducedGateRegistry J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22500000
set_option maxRecDepth 5000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable (S : InstalledRequestInputs W C) (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

structure ResidentAdmissionCarry where
  row : Entry C.mark m native tc tj tw
  site : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw
  receipt : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)×Bool
  oneSite : site=(entrySource (W:=W) C row).result

variable (row : Entry C.mark m native tc tj tw)

/-- The extra cost is for handing off the retained handle, not another
site emission or a second root atlas installation. -/
def submitResidentRowKeepingSite :
    Meter (Option (ResidentAdmissionCarry (W:=W) C pad)) :=
  let probe := S.requests.probes.read row.coord.1.2
  let found := readPublicRequest C S.requests row.wire probe.result.val
  match found.result with
  | none => ⟨none,probe.steps+(found.steps+3)+3+3⟩
  | some r =>
    let X := entrySource (W:=W) C r
    let publish := (cachedJobFromSource C S pad r X.result rfl).install B
    ⟨some ⟨r,X.result,publish.result,rfl⟩,probe.steps+(found.steps+X.steps+publish.steps+4)+3+3⟩

theorem retained_admission_projects_to_actual_ack_and_one_new_handle_charge :
    let paid := submitResidentRowKeepingSite C S pad B row
    (paid.result.map ResidentAdmissionCarry.receipt : Option
      (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)×Bool))=
        (submitResidentRow C S pad B row).result ∧
      paid.steps=(submitResidentRow C S pad B row).steps+3 := by
  let first := S.requests.probes.read row.coord.1.2
  let Q := readPublicRequest C S.requests row.wire first.result.val
  cases found : Q.result with
  | none =>
    change (readPublicRequest C S.requests row.wire (S.requests.probes.read row.coord.1.2).result.val).result=none at found
    unfold submitResidentRowKeepingSite submitResidentRow admitRequest
    dsimp only
    rw [found]
    exact ⟨rfl,rfl⟩
  | some r =>
    change (readPublicRequest C S.requests row.wire (S.requests.probes.read row.coord.1.2).result.val).result=some r at found
    unfold submitResidentRowKeepingSite submitResidentRow admitRequest
    dsimp only
    rw [found]
    exact ⟨rfl,rfl⟩

theorem retaining_the_paid_site_opens_one_root_atlas
    (r : Entry C.mark m native tc tj tw)
    (found : (readPublicRequest C S.requests row.wire (S.requests.probes.read row.coord.1.2).result.val).result=some r) :
    let probe := S.requests.probes.read row.coord.1.2
    let Q := readPublicRequest C S.requests row.wire probe.result.val
    let physical := entrySource (W:=W) C r
    let install := (cachedJobFromSource C S pad r physical.result rfl).install B
    submitResidentRowKeepingSite C S pad B row=
      ⟨some ⟨r,physical.result,install.result,rfl⟩,probe.steps+(Q.steps+physical.steps+install.steps+4)+3+3⟩ := by
  unfold submitResidentRowKeepingSite
  dsimp only
  rw [found]

#print axioms retained_admission_projects_to_actual_ack_and_one_new_handle_charge
#print axioms retaining_the_paid_site_opens_one_root_atlas
end
end J6R111KeptOwnerFlow

