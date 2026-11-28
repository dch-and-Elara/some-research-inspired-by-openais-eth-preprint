import J6R112ExecutedSelectedStartupBase
import J6R112ExecutedSelectedStartupPlan

/-! The physically selected startup and the physically selected outer
count run in succession. The proof-side raw comparator is not a step
in the new execution. -/
namespace J6R112ExecutedSelectedStartup
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat AOracleMachineTime
open J6Mesh J6OrientedHost J7R9Compiler J7R9Subdivision J7R10Plant
open J6R24LegalLayout J6R24MeteredRecursion J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R30GeneratedRootLayout J6R51Ingress
open J6R49RootIngress J6R50RootIngress J6R52FreshShape J6R52FreshExterior J6R15ModeCost
open J6R27PrescribedProbe J6R54PublicFamily J6R57PublicRequest
open J6R110RootWidthChoice J6R110RequestWidthChoice J6R111FreshStartupBinding
open J6R75OuterTime J6R111SelectedGroup J6R31RootResidentTables

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 19000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize m n)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp)

abbrev StartupSelection (fit : base ≤ s ^ 2) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  SelectedCountOnImage (selectedStartup A fit).result

/-- There is one startup meter, and its returned request image is the
argument to the chosen outer count. No independent image is accepted. -/
def runWithActualFreshStartup (fit : base ≤ s ^ 2) (plan : StartupSelection A fit) :
    Meter (A1R10.Word (printedAnswerWidth m base)) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot := selectedStartup A fit
  let counted := countOnThatImage boot.result plan
  ⟨counted.result,boot.steps+counted.steps+5⟩

theorem actual_startup_routes_one_result_to_the_selected_count
    (fit : base ≤ s ^ 2) (plan : StartupSelection A fit) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot := selectedStartup A fit
    let i := boot.result
    let counted := runChosenOuterCount i.compiled i.tables plan.pad plan.prior plan.plans
      plan.sync plan.reserved plan.setups i.compiled.frame i.compiled.positive
    runWithActualFreshStartup A fit plan = ⟨counted.result,boot.steps+counted.steps+5⟩ := rfl

theorem actual_startup_and_selected_count_keep_each_real_debit
    (fit : base ≤ s ^ 2) (plan : StartupSelection A fit) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot := selectedStartup A fit
    let words := initialPaidWords A fit
    let input := originalInputsAtGeneratedWords A words.result
    let W := chooseWidths m n (fresh_source_native_fits F order)
    let imageFee := (buildRequestImage W input).steps
    let old := rawComparisonOnThatImage boot.result plan
    let out := runWithActualFreshStartup A fit plan
    out.result = old.result ∧ out.steps =
      ordinalFee (chosenQ m) base + imageFee + old.steps + paidSetupsOnThatImage boot.result plan + 5 := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot := selectedStartup A fit
  let words := initialPaidWords A fit
  let input := originalInputsAtGeneratedWords A words.result
  let W := chooseWidths m n (fresh_source_native_fits F order)
  let imageFee := (buildRequestImage W input).steps
  let old := rawComparisonOnThatImage boot.result plan
  let counted := countOnThatImage boot.result plan
  let added := paidSetupsOnThatImage boot.result plan
  have Afee : boot.steps=ordinalFee (chosenQ m) base+imageFee :=
    (same_request_image_and_one_real_width_emission A fit).2
  have paid : Delta counted old added := the_selected_image_count_pays_its_actual_setups boot.result plan
  change counted.result = old.result ∧
    boot.steps+counted.steps+5=ordinalFee (chosenQ m) base+imageFee+old.steps+added+5
  refine ⟨paid.value,?_⟩
  rw [Afee,paid.fee]
  simp only [Nat.add_assoc]

#print axioms runWithActualFreshStartup
#print axioms actual_startup_routes_one_result_to_the_selected_count
#print axioms actual_startup_and_selected_count_keep_each_real_debit
end
end J6R112ExecutedSelectedStartup

