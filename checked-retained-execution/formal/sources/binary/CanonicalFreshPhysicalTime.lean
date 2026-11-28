import J6R118FinalRawMeasuredClock
import CanonicalFreshPhysicalCount

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
local notation "sourceNative" => (Paper6SourceSize.sourceNativeSize F order)
local notation "subdivisions" => (nSubdiv Graph)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp) (fit : base ≤ physicalSize (nWires (guardedInOrder F order.roster))
    (Paper6SourceSize.sourceNativeSize F order)^2)

open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6R32RootGeneratedRegistryInputs
open J6R14ZeroMode J1PPrinted J6R14LayoutCost J6R36SharedGateway

variable (groups : ActualPhysicalStartupPlan A fit)
/-- Count and full measured clock on the very same named binary meter.
The root schedule uses sourceNative. The factor width counts subdivisions. -/
theorem binary_order_ready_fresh_count_and_time
    (prepCap rootCap : ℕ)
    (data : FreshSourcePreparationAndRoots A fit groups (freshBinaryExactRows (F:=F) (order:=order)) prepCap rootCap)
    (basePositive : 0<base) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage A fit) := selectedStartup A fit
    let D := boot.result.compiled
    let frame := D.frame
    let fd := (freshFieldResult F order).f.natDegree
    let p := J6SourcePrecision.printed NW base
    let out := runFreshBinaryOrderCount A fit groups
    let caps := phaseCapsOnTheFreshOriginalInputs A fit groups (freshBinaryExactRows (F:=F) (order:=order)) prepCap rootCap data
    let slots := actualReceiptSlotRoof (m:=NW) (native:=sourceNative) (tc:=centreWidth NW) (tj:=sampleWidth NW)
      (tw:=magnitudeWidth NW) (f:=(freshFieldResult F order).f) (base:=base) (ell:=ell)
      (literalFreshGroupRoof A fit groups (freshBinaryExactRows (F:=F) (order:=order)) caps)
    let pads := (exactPadOrder NW (K NW) (printedHalf NW) (constantRootWord NW)).length
    let site := rootSiteFee fd NW (literalDegree NW sourceNative) ell p frame.hp+(literalDegree NW sourceNative+1)*slots
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤boot.steps+(stablePadBudget (a NW) (K NW) (printedHalf NW) (printedRankWidth NW)+
        legalRootBudget p (printedFactorWidth NW subdivisions) (printedAnswerWidth NW base)
           ell frame.words.length (printedRankWidth NW-a NW+13*a NW) NW pads+8+
            gatheredOracleFee NW frame.words.length ell p site)+5 := by
  exact original_ready_fresh_run_counts_and_pays_the_source_clock A fit groups
    (freshBinaryExactRows (F:=F) (order:=order))
    prepCap rootCap data basePositive

#print axioms binary_order_ready_fresh_count_and_time
end

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "NW" => (nWires Graph)
local notation "sourceNative" => (Paper6SourceSize.sourceNativeSize F order)
local notation "subdivisions" => (nSubdiv Graph)
local notation "literalBase" => (Paper6SourceSize.sourceInitialPrecision F order)
omit [Nonempty V] in
private theorem canonicalClockSourcePrecisionFits (F : CNF V) (order : DeclaredOrder V) :
    Paper6SourceSize.sourceInitialPrecision F order ≤
      physicalSize (nWires (guardedInOrder F order.roster))
        (Paper6SourceSize.sourceNativeSize F order)^2 := by
  simpa only [Paper6SourceSize.sourcePaddedSize] using
    Paper6SourceSize.sourceInitialPrecision_le_sq F order

open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6R32RootGeneratedRegistryInputs
open J6R14ZeroMode J1PPrinted J6R14LayoutCost J6R36SharedGateway

attribute [local irreducible] Paper6SourceSize.sourceInitialPrecision selectedStartup

local notation "literalFit" => (canonicalClockSourcePrecisionFits F order)
variable {h d j r c e kp : ℕ}

theorem binary_order_at_literal_source_precision_counts_and_time
    (A : RawStartup F order h d j r c e literalBase 1 kp)
    (groups : ActualPhysicalStartupPlan (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e)
      (base:=literalBase) (ell:=1) (kp:=kp) A literalFit)
    (prepCap rootCap : ℕ)
    (data : FreshSourcePreparationAndRoots (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit groups (freshBinaryExactRows (F:=F) (order:=order)) prepCap rootCap) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit) :=
      selectedStartup (F:=F) (order:=order)
        (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit
    let D := boot.result.compiled
    let frame := D.frame
    let fd := (freshFieldResult F order).f.natDegree
    let p := J6SourcePrecision.printed NW literalBase
    let out := runFreshBinaryOrderCount (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit groups
    let caps := phaseCapsOnTheFreshOriginalInputs (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit groups (freshBinaryExactRows (F:=F) (order:=order)) prepCap rootCap data
    let slots := actualReceiptSlotRoof (m:=NW) (native:=sourceNative) (tc:=centreWidth NW) (tj:=sampleWidth NW)
      (tw:=magnitudeWidth NW) (f:=(freshFieldResult F order).f) (base:=literalBase) (ell:=1)
      (literalFreshGroupRoof (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit groups (freshBinaryExactRows (F:=F) (order:=order)) caps)
    let pads := (exactPadOrder NW (K NW) (printedHalf NW) (constantRootWord NW)).length
    let site := rootSiteFee fd NW (literalDegree NW sourceNative) 1 p frame.hp+(literalDegree NW sourceNative+1)*slots
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤boot.steps+(stablePadBudget (a NW) (K NW) (printedHalf NW) (printedRankWidth NW)+
        legalRootBudget p (printedFactorWidth NW subdivisions) (printedAnswerWidth NW literalBase)
           1 frame.words.length (printedRankWidth NW-a NW+13*a NW) NW pads+8+
            gatheredOracleFee NW frame.words.length 1 p site)+5 := by
  exact binary_order_ready_fresh_count_and_time (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=literalBase) (ell:=1) (kp:=kp) A literalFit groups prepCap rootCap data
    (Paper6SourceSize.sourceInitialPrecision_pos F order)

#print axioms binary_order_at_literal_source_precision_counts_and_time
end
end J6R114PrescribedReceipts
