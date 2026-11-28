import J6R114ImageReceipts
import J6R114AdmittedReceipts

/-! The chosen plan is parameterized by the returned image itself;
admission data cannot come from a second startup or a distinct request. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer

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

structure AdmittedExecutionImage (image : RequestImage W I) where
  pad : ℕ
  prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)
  sync : prior.synced
  reserved : ∀ h∈prior.headers,h.id.bits.take kp≠image.compiled.mark.bits
  resume : OnTheReturnedPayload image.compiled image.tables pad prior

variable (image : RequestImage W I) (plan : AdmittedExecutionImage image)

def exactCountFromKeptAdmissions : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  paidCountOnImage image (consumeTheActualAdmittedRows image.compiled image.tables
    plan.pad plan.prior plan.sync plan.reserved plan.resume)

theorem count_with_one_actual_admission_at_every_address
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (exactCountFromKeptAdmissions image plan).result.val=answer :=
  the_exact_addressed_image_count image (consumeTheActualAdmittedRows image.compiled image.tables
    plan.pad plan.prior plan.sync plan.reserved plan.resume) positiveBase zeroOpening answer count

#print axioms exactCountFromKeptAdmissions
#print axioms count_with_one_actual_admission_at_every_address
end
end J6R114PrescribedReceipts

