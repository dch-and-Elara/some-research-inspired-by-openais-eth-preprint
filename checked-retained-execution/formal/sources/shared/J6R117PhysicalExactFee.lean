import J6R116PhysicalRetainedImage

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

open J6R111KeptOwnerFlow

theorem physical_row_charges_its_actual_admission_preparation_and_continuation
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry image.compiled.mark m native tc tj tw)
    (sameRow : r=sourceRow (W:=W) image.compiled i j g)
    (written : r∈image.tables.requests.rows) :
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r sameRow
    let a := posted.result
    let data := Q.acquire i j g r sameRow a
    let A := data.result
    let native := runRetainedExterior a.payload.site A.machine a.payload.receipt.1 a.owns
      A.first A.drivers A.exterior A.retire
    ((physicalRowsOnThatImage image Q i j g r sameRow written).run).steps =
      posted.steps+(data.steps+native.steps+4)+3 := by
  let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r sameRow
  let a := posted.result
  let data := Q.acquire i j g r sameRow a
  let A := data.result
  let run := measuredRetainedPhysicalGroup a.payload data a.owns a.live
  let native := runRetainedExterior a.payload.site A.machine a.payload.receipt.1 a.owns
    A.first A.drivers A.exterior A.retire
  have hi : a.payload.site.centre=i := (congrArg StableExterior.centre a.selectedSite).trans rfl
  have hj : a.payload.site.sample=j := (congrArg StableExterior.sample a.selectedSite).trans rfl
  have hg : a.payload.site.group=g := (congrArg StableExterior.group a.selectedSite).trans rfl
  change posted.steps+(typedOriginalGroup hi hj hg run).run.steps+3=
    posted.steps+(data.steps+native.steps+4)+3
  rw [typed_group_does_not_change_the_actual_steps hi hj hg run,
    the_paid_group_runs_from_that_one_returned_bank_and_data a.payload data a.owns a.live]

#print axioms physical_row_charges_its_actual_admission_preparation_and_continuation
end
end J6R114PrescribedReceipts

