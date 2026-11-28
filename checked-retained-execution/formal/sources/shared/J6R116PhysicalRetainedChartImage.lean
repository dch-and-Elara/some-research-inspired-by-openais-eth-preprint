import J6R116PhysicalRetainedImage
import J6R116ReadyRetainedChart

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

open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable

variable (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result=
  OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))

def mountTheChartOnEveryChosenActualGroup : PhysicalRetainedImagePlan image where
  pad := Q.pad
  prior := Q.prior
  sync := Q.sync
  reserved := Q.reserved
  acquire := fun i j g r sameRow a =>
    prepareWithPaidOriginalOrder a.payload (Q.acquire i j g r sameRow a) bytes
  acquireScale := fun i j g r sameRow a => Q.acquireScale i j g r sameRow a

theorem posted_and_mounted_payload_has_source_scale
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let P := mountTheChartOnEveryChosenActualGroup image Q bytes
    let row := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables P.pad P.prior P.sync P.reserved i j g row rfl
    let actual := P.acquire i j g row rfl posted.result
    actual.result.size=physicalSize m native ∧ actual.result.constant=2 ∧
      HEq actual.result.selector (G.selector ell) :=
  actual_posted_payload_has_source_scale image (mountTheChartOnEveryChosenActualGroup image Q bytes) i j g

theorem each_admitted_group_uses_this_full_paid_chart_producer
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (r : Entry image.compiled.mark m native tc tj tw)
    (sameRow : r=sourceRow (W:=W) image.compiled i j g)
    (a : AdmittedAtAddress image.compiled image.tables Q.pad Q.prior i j g r) :
    let old := Q.acquire i j g r sameRow a
    let chart := mountFullChart old.result.prepared bytes
    let paid := (mountTheChartOnEveryChosenActualGroup image Q bytes).acquire i j g r sameRow a
    paid.result.drivers.masks=chart.result ∧
    paid.steps=old.steps+chart.steps+4 ∧
    paid.steps≤old.steps+3660*old.result.size^5+4 :=
  the_retained_driver_uses_the_one_paid_chart_and_its_printed_bound a.payload (Q.acquire i j g r sameRow a) bytes

#print axioms mountTheChartOnEveryChosenActualGroup
#print axioms posted_and_mounted_payload_has_source_scale
#print axioms each_admitted_group_uses_this_full_paid_chart_producer
end
end J6R114PrescribedReceipts

