import J6R117PhysicalExactFee
import J6R117PhysicalOuterTime

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

/-- A report on the three actual operations at each original address.
The canonical row is used only as a proof index: the outer program
still emits its row using the measured head. -/
structure PhysicalGroupPhaseCaps where
  admission : ℕ
  preparation : ℕ
  contraction : ℕ
  paid : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
    let r := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r rfl
    let a := posted.result
    let P := Q.acquire i j g r rfl a
    let A := P.result
    let run := runRetainedExterior a.payload.site A.machine a.payload.receipt.1 a.owns
      A.first A.drivers A.exterior A.retire
    posted.steps≤admission ∧ P.steps≤preparation ∧ run.steps≤contraction

theorem charge_bound_on_each_same_image_group
    (bounds : PhysicalGroupPhaseCaps image Q)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    (actualSameImageReceipts image Q i j g (prepareHead W i j).result rfl).run.steps≤
      ordinalFee 6 63+6*KeyWidth kp tc tj+17+
        bounds.admission+bounds.preparation+bounds.contraction+10 := by
  let D := image.compiled
  let S := image.tables
  let issued := emitEntry D.mark (i,j) (prepareHead W i j).result g
  let r := sourceRow (W:=W) D i j g
  let posted := admitTheEmittedRow D S Q.pad Q.prior Q.sync Q.reserved i j g r rfl
  let a := posted.result
  let data := Q.acquire i j g r rfl a
  let A := data.result
  let run := runRetainedExterior a.payload.site A.machine a.payload.receipt.1 a.owns
     A.first A.drivers A.exterior A.retire
  let written := canonical_source_row_is_resident D S i j g
  have cost0 := each_group_pays_its_emission_and_its_one_continuation D S
      (physicalRowsOnThatImage image Q) i j g (prepareHead W i j).result rfl
  obtain ⟨_,_,cost0⟩ := cost0
  change (actualSameImageReceipts image Q i j g (prepareHead W i j).result rfl).run.steps =
     issued.steps+((physicalRowsOnThatImage image Q i j g r rfl written).run).steps+3 at cost0
  have cost := physical_row_charges_its_actual_admission_preparation_and_continuation image Q i j g r rfl written
  change ((physicalRowsOnThatImage image Q i j g r rfl written).run).steps =
    posted.steps+(data.steps+run.steps+4)+3 at cost
  have outFee := (actual_entry_wires W D.mark ((i,j),g)).2.2.2.2.2
  change issued.steps=ordinalFee 6 g.val+6*KeyWidth kp tc tj+17 at outFee
  have gCap : ordinalFee 6 g.val≤ordinalFee 6 63 :=
    ordinal_fee_monotone 6 (Nat.le_of_lt_succ g.isLt)
  obtain ⟨ha,hp,hr⟩ := bounds.paid i j g
  change posted.steps≤bounds.admission at ha
  change data.steps≤bounds.preparation at hp
  change run.steps≤bounds.contraction at hr
  rw [cost0,cost,outFee]
  omega

#print axioms charge_bound_on_each_same_image_group
end
end J6R114PrescribedReceipts

