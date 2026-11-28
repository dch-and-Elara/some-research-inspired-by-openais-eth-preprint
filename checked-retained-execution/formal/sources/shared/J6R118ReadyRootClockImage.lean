import J6R118ReadyRootClockCore
import J6R116PhysicalRetainedImage

/-! Specialize the ready-root tariff to the exact admitted, prepared row
used by the original image. No independent prepared payload is supplied. -/
namespace J6R118ReadyRootClock
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
set_option maxHeartbeats 7200000
set_option maxSynthPendingDepth 10

open J6R114PrescribedReceipts
noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]


variable (image : RequestImage W I) (Q : PhysicalRetainedImagePlan image)

open J6R111KeptOwnerFlow J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R57ScopeFee J6R32RootGeneratedRegistryInputs J6R68AbsolutePrescribed


/-- Take the seed from the selected source schedule and the actual posted
admission. This also applies to the chart-mounted plan, whose scale and
selector are preserved by construction. -/
theorem actual_posted_ready_root_has_its_source_seed
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (baseFit : base≤2*physicalSize m native) :
    let row := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g row rfl
    let a := posted.result.payload
    let actual := (Q.acquire i j g row rfl posted.result).result
    AbsoluteSeed actual.size actual.constant (exteriorChild G ell a.site.centre a.site.sample a.site.group) := by
  let row := sourceRow (W:=W) image.compiled i j g
  let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g row rfl
  let a := posted.result.payload
  let actual := (Q.acquire i j g row rfl posted.result).result
  have scale := actual_posted_payload_has_source_scale image Q i j g
  exact loaded_original_scale_has_its_prescribed_seed a actual scale.1 scale.2.1 baseFit

/-- Exactly the contraction inequality in `PhysicalGroupPhaseCaps.paid`.
`sourceRow` only fixes the proof index, and costs are read from the
objects returned by admission and preparation on that index. -/
theorem ready_contraction_on_the_original_posted_row
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    {ptr : ℕ} (tails : SavedDirectoryTails ptr) (α : ℕ) :
    let r := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g r rfl
    let a := posted.result
    let P := Q.acquire i j g r rfl a
    let A := P.result
    let run := runRetainedExterior a.payload.site A.machine a.payload.receipt.1 a.owns
      A.first A.drivers A.exterior A.retire
    ∀ C : ReadyContractionInputs a.payload A tails,
      readyRootContractionRoof a.payload A C≤α → run.steps≤α := by
  dsimp only
  intro C fits
  exact ready_root_contracts_on_its_paid_bank_with_alpha _ _ C _ α fits

#print axioms actual_posted_ready_root_has_its_source_seed
#print axioms ready_contraction_on_the_original_posted_row
end
end J6R118ReadyRootClock
