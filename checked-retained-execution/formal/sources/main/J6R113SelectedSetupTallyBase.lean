import J6R112ExecutedSelectedStartupPlan

/-! The exact additional debit of the same R112 selected run.
The publication snapshot is only the name of the acknowledged bank
in the existing R111 fee identity, not a second acquisition. -/
namespace J6R113SelectedSetupTally
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

open J6R22Active J6R66.BootPeak J6R112ExecutedSelectedStartup

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4500

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I) (plan : SelectedCountOnImage image)

local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))

/-- The original R111 selection on the actual acknowledged bank.
No new price for obtaining the chosen machine is imposed. -/
def realAcquisition (i : Centre) (j : Sample) (g : Fin 64) : ℕ :=
  let D := image.compiled
  let S := image.tables
  let r := sourceRow (W:=W) D i j g
  let h := canonical_source_row_is_resident D S i j g
  let ack := (accepted_entry_installs_that_actual_job D S plan.pad plan.prior r plan.sync plan.reserved h).1
  let own := literal_exterior_owns_the_installed_head D S plan.pad plan.prior r (actualExterior (W:=W) D r) rfl
  ((plan.setups i j g).paidChosen (publishedBank D S plan.pad plan.prior r) ack own).steps

def realChart (i : Centre) (j : Sample) (g : Fin 64) : ℕ :=
  (plan.setups i j g).paidChart.steps

def totalAcquisition : ℕ :=
  ∑ i : Centre, ∑ j : Sample, ∑ g : Fin 64, realAcquisition image plan i j g

def totalChart : ℕ :=
  ∑ i : Centre, ∑ j : Sample, ∑ g : Fin 64, realChart image plan i j g

def rosterVolume (m native : ℕ) : ℕ :=
  (m+1)*(literalDegree m native+1)*64

theorem actual_paid_setup_sum_exact :
    paidSetupsOnThatImage image plan =
      ∑ i : Centre, ∑ j : Sample, ∑ g : Fin 64,
        (realAcquisition image plan i j g + realChart image plan i j g + 3) := by
  simp only [paidSetupsOnThatImage,List.sum_ofFn]
  refine Finset.sum_congr rfl (fun i _=>?_)
  simp only [oneSiteSelectedExtra,probeOrder,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  rfl

theorem sum_constant_over_actual_roster (v : ℕ) :
    (∑ _ : Centre, ∑ _ : Sample, ∑ _ : Fin 64, v)=rosterVolume m native*v := by
  simp [rosterVolume, Finset.sum_const, Nat.mul_assoc]

theorem actual_paid_setup_sum_by_field :
    paidSetupsOnThatImage image plan =
      totalAcquisition image plan+totalChart image plan+rosterVolume m native*3 := by
  rw [actual_paid_setup_sum_exact]
  simp only [Finset.sum_add_distrib]
  rw [sum_constant_over_actual_roster]
  rfl

theorem selected_image_pays_the_expanded_actual_additional_bill :
    (countOnThatImage image plan).steps =
      (rawComparisonOnThatImage image plan).steps +
        (totalAcquisition image plan+totalChart image plan+rosterVolume m native*3) := by
  rw [(the_selected_image_count_pays_its_actual_setups image plan).fee,actual_paid_setup_sum_by_field]

#print axioms actual_paid_setup_sum_exact
#print axioms sum_constant_over_actual_roster
#print axioms actual_paid_setup_sum_by_field
#print axioms selected_image_pays_the_expanded_actual_additional_bill
end
end J6R113SelectedSetupTally
