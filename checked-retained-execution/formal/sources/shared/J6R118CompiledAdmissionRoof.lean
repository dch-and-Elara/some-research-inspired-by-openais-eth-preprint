import J6R116PhysicalRetainedImage
import J6R107ActualOuter
import J6R75OuterTimeBounds

/-! Assembly over the one returned request image. For each real group
address, the preparer takes the actual held payload; the original
addresses index the result, not a second evaluation. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6 J6R34OfficialGateway
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer J6R52FreshExterior J6R111KeptOwnerFlow

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 15000000
set_option maxSynthPendingDepth 10

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]


variable (image : RequestImage W I) (Q : PhysicalRetainedImagePlan image)

open J6R111KeptOwnerFlow J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R106OuterBudget

def originalCompiledAdmissionRoof : ℕ :=
  let D := image.compiled
  let S := image.tables
  submittedRowRoof m native (KeyWidth kp tc tj) f.natDegree
    (selectedPublicationClock D S Q.pad Q.prior)+3

theorem actual_retained_admission_uses_the_compiled_publication_roof
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let D := image.compiled
    let S := image.tables
    let r := sourceRow (W:=W) D i j g
    let posted := admitTheEmittedRow D S Q.pad Q.prior Q.sync Q.reserved i j g r rfl
    posted.steps≤originalCompiledAdmissionRoof image Q := by
  let D := image.compiled
  let S := image.tables
  let r := sourceRow (W:=W) D i j g
  let job := cachedExteriorJob D S Q.pad r
  let install := selectedPublicationClock D S Q.pad Q.prior
  have actual : (job.install Q.prior).steps ≤ install := by
    change ((cachedExteriorJob D S Q.pad (sourceRow (W:=W) D i j g)).install Q.prior).steps ≤ install
    rw [literal_outer_publication_is_the_true_publish_fee D S Q.pad Q.prior i j g Q.sync Q.reserved]
    exact compiled_publication_obeys_one_real_bank_clock D S Q.pad Q.prior r
  have ordinary := true_literal_submit_has_the_local_roof D S Q.pad Q.prior i j g install actual
  have fees := (retained_admission_projects_to_actual_ack_and_one_new_handle_charge D S Q.pad Q.prior r).2
  change (submitResidentRowKeepingSite D S Q.pad Q.prior r).steps ≤
    submittedRowRoof m native (KeyWidth kp tc tj) f.natDegree install + 3
  rw [fees]
  exact Nat.add_le_add_right ordinary 3

#print axioms actual_retained_admission_uses_the_compiled_publication_roof
end
end J6R114PrescribedReceipts

