import J6R114EmittedReceipts
import J6R112ExecutedSelectedStartupPlan

/-! Generic image interface: source address and all installed tables are
indexed by the same actual returned image. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4800
set_option maxHeartbeats 20000000
set_option maxSynthPendingDepth 10

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I)

abbrev PaidRowsOnImage := AtWrittenRow image.compiled image.tables

def paidCountOnImage (use : PaidRowsOnImage image) : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  runActualReceiptCount image.compiled image.tables image.compiled.frame image.compiled.positive
    (addressedPaidReceipts image.compiled image.tables use)

theorem the_exact_addressed_image_count (use : PaidRowsOnImage image)
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (paidCountOnImage image use).result.val=answer :=
  (actual_receipts_give_exact_count_and_each_its_own_cost image.compiled image.tables image.compiled.frame
    image.compiled.positive (addressedPaidReceipts image.compiled image.tables use) positiveBase
    zeroOpening answer count).1

#print axioms paidCountOnImage
#print axioms the_exact_addressed_image_count
end
end J6R114PrescribedReceipts

