import J6R111SelectedOuter

/-! The selected outer evaluator is indexed by the returned R57 request
image. Its count frame, marked rows, probe bank and compiled root all
come from the explicit image argument. The per-row producers remain
the original typed and metered R111 setup witnesses. -/
namespace J6R112ExecutedSelectedStartup
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway A1R12
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted
open J6R36SharedGateway J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout
open J6R111SelectedGroup J6R12Blueprint J6R31RootResidentTables J6OrientedHostEval

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 24000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

/-- There is no independent compiler, request table, or receiving frame.
The prior and the original R111 selected suppliers are explicit. -/
structure SelectedCountOnImage (image : RequestImage W I) where
  pad : ℕ
  prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)
  size : ℕ
  constant : ℕ
  rate : ℕ
  rankWidth : ℕ
  bounds : RootBounds size constant f
  plans : RawGroupPlans image.compiled image.tables pad prior bounds rate rankWidth
  sync : prior.synced
  reserved : ∀ x∈prior.headers, x.id.bits.take kp ≠ image.compiled.mark.bits
  setups : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
    PaidSetupForPlan image.compiled image.tables pad prior
      (sourceRow (W:=W) image.compiled i j g) (plans i j g)

variable (image : RequestImage W I) (plan : SelectedCountOnImage image)

def countOnThatImage : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  runChosenOuterCount image.compiled image.tables plan.pad plan.prior plan.plans
    plan.sync plan.reserved plan.setups image.compiled.frame image.compiled.positive

/-- Comparison only; this run is not evaluated during the new execution. -/
def rawComparisonOnThatImage : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  runRawOuterCount image.compiled image.tables plan.pad plan.prior plan.plans
    plan.sync plan.reserved image.compiled.frame image.compiled.positive

def paidSetupsOnThatImage : ℕ :=
  (List.ofFn (oneSiteSelectedExtra image.compiled image.tables plan.pad plan.prior plan.plans
    plan.sync plan.reserved plan.setups)).sum

theorem the_selected_image_count_pays_its_actual_setups :
    Delta (countOnThatImage image plan) (rawComparisonOnThatImage image plan)
      (paidSetupsOnThatImage image plan) :=
  chosen_outer_count_includes_every_actual_setup image.compiled image.tables plan.pad plan.prior
    plan.plans plan.sync plan.reserved plan.setups image.compiled.frame image.compiled.positive

theorem the_selected_image_count_is_the_guarded_count
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool //
      coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (countOnThatImage image plan).result.val=answer := by
  rw [(the_selected_image_count_pays_its_actual_setups image plan).value]
  exact (exact_guarded_count_from_the_actual_outer_runs image.compiled image.tables plan.pad plan.prior
    plan.plans plan.sync plan.reserved image.compiled.frame image.compiled.positive
    positiveBase zeroOpening answer count).1

#print axioms countOnThatImage
#print axioms the_selected_image_count_pays_its_actual_setups
#print axioms the_selected_image_count_is_the_guarded_count
end
end J6R112ExecutedSelectedStartup

