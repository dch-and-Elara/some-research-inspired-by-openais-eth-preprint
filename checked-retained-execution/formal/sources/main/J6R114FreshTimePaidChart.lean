import J6R113FreshTime
import J6R113SelectedSetupTallyChart

/-! Join the R113 selected time and actual setup tariff on a single
executed fresh startup and its own selected count. No synthetic bill
or second runtime is used. -/
namespace J6R114FreshTimePaidChart
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest J6R31RootResidentTables
open J6R110RootWidthChoice J6R110RequestWidthChoice J6R111FreshStartupBinding
open J6R75OuterTime J6R111SelectedGroup J6R79Numeric J6R102FinalPhase
open J6R112ExecutedSelectedStartup J6R112GuardedInputBinding
open J6R113SelectedTime J6R113SelectedSetupTally
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5000
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "GuardedGraph" => (guardedInOrder F order.roster)
local notation "PhysicalSize" => (physicalSize (nWires GuardedGraph) (Paper6SourceSize.sourceNativeSize F order))
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp)

theorem actual_fresh_execution_counts_with_the_paid_canonical_chart_tariff
    (fit : base ≤ PhysicalSize^2) (plan : StartupSelection A fit)
    (K0 producerPower leafPower rank : ℕ) (coefficients : ProducerCoefficients)
    (rankEq : letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
        ⟨(generated_fresh_field_is_permitted F order).2⟩
      plan.rankWidth=rank+1)
    (profile : letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
        ⟨(generated_fresh_field_is_permitted F order).2⟩
      let image := (selectedStartup A fit).result
      let R : RawGroupPlans image.compiled image.tables plan.pad plan.prior plan.bounds plan.rate (rank+1) := rankEq ▸ plan.plans
      ∀ (i : J6Recovery.Addr (nWires GuardedGraph))
        (j : Fin (J6R14ZeroMode.literalDegree (nWires GuardedGraph) (Paper6SourceSize.sourceNativeSize F order)+1)) (g : Fin 64),
        Nonempty (SelectedPlanSource image.compiled image.tables plan.pad plan.prior
          (sourceRow image.compiled i j g) (R i j g) K0 producerPower leafPower coefficients))
    (positiveBase : 0<base)
    (mounted : letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
        ⟨(generated_fresh_field_is_permitted F order).2⟩
      CanonicalCharts (selectedStartup A fit).result plan) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot := selectedStartup A fit
    let out := runWithActualFreshStartup A fit plan
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
    out.steps ≤ boot.steps+sameImageRawClock boot.result plan K0 producerPower leafPower coefficients+
      (totalAcquisition boot.result plan+
        rosterVolume (nWires GuardedGraph) (Paper6SourceSize.sourceNativeSize F order)*(3660*plan.size^5+3))+5 := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot := selectedStartup A fit
  have H := actual_fresh_execution_keeps_the_certified_time A fit plan
    K0 producerPower leafPower rank coefficients rankEq profile positiveBase
  have B := paid_setups_fit_the_actual_canonical_chart_bill boot.result plan mounted
  refine ⟨H.1,H.2.trans ?_⟩
  exact Nat.add_le_add_right
    (Nat.add_le_add_left B (boot.steps+sameImageRawClock boot.result plan K0 producerPower leafPower coefficients)) 5

#print axioms actual_fresh_execution_counts_with_the_paid_canonical_chart_tariff
end
end J6R114FreshTimePaidChart
