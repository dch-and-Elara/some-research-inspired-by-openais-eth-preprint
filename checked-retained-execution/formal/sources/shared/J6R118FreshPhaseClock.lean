import J6R117FreshPhysicalClock
import J6R118PhysicalGroupBudget

/-! The physically selected startup and the physically selected outer
count run in succession. The proof-side raw comparator is not a step
in the new execution. -/
namespace J6R114PrescribedReceipts
open J6R112ExecutedSelectedStartup J6R112GuardedInputBinding AOracleMachineTimeTape
open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable
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
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "NW" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize NW n)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp) (fit : base ≤ physicalSize (nWires (guardedInOrder F order.roster))
    (Paper6SourceSize.sourceNativeSize F order)^2)

open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6R32RootGeneratedRegistryInputs
open J6R14ZeroMode J1PPrinted J6R14LayoutCost J6R36SharedGateway

variable (groups : ActualPhysicalStartupPlan A fit)
variable (bytes : (canonicalTable ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree)+1)).result=
    OldOrderedBytes ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree))
      (full_probe_fit ((freshFieldResult F order).f.natDegree)))

abbrev LiteralFreshPhaseCaps :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup A fit
  let plan := mountTheChartOnEveryChosenActualGroup boot.result groups bytes
  PhysicalGroupPhaseCaps boot.result plan

variable (bounds : LiteralFreshPhaseCaps A fit groups bytes)

def literalFreshGroupRoof : ℕ :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  ordinalFee 6 63+6*KeyWidth kp (centreWidth NW) (sampleWidth NW)+17+
    bounds.admission+bounds.preparation+bounds.contraction+10

theorem literal_fresh_group_budget_is_for_the_same_reached_group :
    ActualFreshGroupCap A fit groups bytes (literalFreshGroupRoof A fit groups bytes bounds) := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup A fit
  let plan := mountTheChartOnEveryChosenActualGroup boot.result groups bytes
  intro i j g
  exact charge_bound_on_each_same_image_group boot.result plan bounds i j g


theorem literal_fresh_exact_count_with_its_actual_phase_tariffs
    (basePositive : 0<base) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage A fit) := selectedStartup A fit
    let D := boot.result.compiled
    let frame := D.frame
    let fd := (freshFieldResult F order).f.natDegree
    let p := J6SourcePrecision.printed NW base
    let out := runFreshPhysicallyRetainedCount A fit groups bytes
    let slots := actualReceiptSlotRoof (m:=NW) (native:=n) (tc:=centreWidth NW) (tj:=sampleWidth NW)
      (tw:=magnitudeWidth NW) (f:=(freshFieldResult F order).f) (base:=base) (ell:=ell)
      (literalFreshGroupRoof A fit groups bytes bounds)
    let pads := (exactPadOrder NW (K NW) (printedHalf NW) (constantRootWord NW)).length
    let site := rootSiteFee fd NW (literalDegree NW n) ell p frame.hp+(literalDegree NW n+1)*slots
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤boot.steps+(stablePadBudget (a NW) (K NW) (printedHalf NW) (printedRankWidth NW)+
        legalRootBudget p (printedFactorWidth NW (nSubdiv Graph)) (printedAnswerWidth NW base)
           ell frame.words.length (printedRankWidth NW-a NW+13*a NW) NW pads+8+
            gatheredOracleFee NW frame.words.length ell p site)+5 := by
  exact fresh_physical_count_and_outer_time_use_the_same_meter A fit groups bytes
    (literalFreshGroupRoof A fit groups bytes bounds)
    (literal_fresh_group_budget_is_for_the_same_reached_group A fit groups bytes bounds) basePositive

#print axioms literal_fresh_group_budget_is_for_the_same_reached_group
#print axioms literal_fresh_exact_count_with_its_actual_phase_tariffs
end
end J6R114PrescribedReceipts

