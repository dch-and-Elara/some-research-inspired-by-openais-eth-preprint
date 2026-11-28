import J6R113SelectedSetupTallyBase
import J6R110CanonicalCoverageMount

/-! The published chart tariff applies only when the same performed chart
Meter is the verified full mount, not just when their returned values
happen to agree. The real acquisition fees remain an explicit sum. -/
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
open J6R109CanonicalProbeTable J6R110CanonicalMount J6R110CanonicalCoverage

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
local notation "E" => f.natDegree
local notation "Fdeg" => (fullProbeDegree f.natDegree)

def CanonicalCharts : Prop :=
  ∃ bytes : (canonicalTable E (Fdeg+1)).result=OldOrderedBytes E Fdeg (full_probe_fit E),
    ∀ (i : Centre) (j : Sample) (g : Fin 64),
      (plan.setups i j g).paidChart = mountFullChart (plan.plans i j g).prep bytes

theorem paid_setups_fit_the_actual_canonical_chart_bill
    (mounted : CanonicalCharts image plan) :
    paidSetupsOnThatImage image plan ≤
      totalAcquisition image plan+rosterVolume m native*(3660*plan.size^5+3) := by
  obtain ⟨bytes,mount⟩ := mounted
  have cap (i : Centre) (j : Sample) (g : Fin 64) :
      realChart image plan i j g ≤ 3660*plan.size^5 := by
    change (plan.setups i j g).paidChart.steps≤_
    rw [mount i j g]
    exact (actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace
      (plan.plans i j g).prep bytes).2.2.2.2.1
  have T : totalChart image plan ≤ rosterVolume m native*(3660*plan.size^5) := by
    unfold totalChart
    rw [←sum_constant_over_actual_roster (m:=m) (native:=native) (3660*plan.size^5)]
    refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun g _ => ?_)))
    exact cap i j g
  rw [actual_paid_setup_sum_by_field, Nat.mul_add]
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_right (Nat.add_le_add_left T (totalAcquisition image plan)) (rosterVolume m native*3)

#print axioms paid_setups_fit_the_actual_canonical_chart_bill
end
end J6R113SelectedSetupTally
