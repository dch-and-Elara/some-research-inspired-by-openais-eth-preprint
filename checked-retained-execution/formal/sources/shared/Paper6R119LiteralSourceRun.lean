import J6R118FinalRawMeasuredClock
import Paper6R119PhysicalSpace

/-! The declared-source precision specialization of the paid startup and
count/clock. The initial ordinal is emitted by the normal paid producer. -/
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
variable {h d j r c e kp : ℕ}
local notation "P₀" => (Paper6SourceSize.sourceInitialPrecision F order)
omit [Nonempty V] in
private theorem literalSourcePrecisionFits (F : CNF V) (order : DeclaredOrder V) :
    Paper6SourceSize.sourceInitialPrecision F order ≤
      physicalSize (nWires (guardedInOrder F order.roster))
        (Paper6SourceSize.sourceNativeSize F order)^2 := by
  simpa only [Paper6SourceSize.sourcePaddedSize] using
    Paper6SourceSize.sourceInitialPrecision_le_sq F order

local notation "P₀Fit" => (literalSourcePrecisionFits F order)
attribute [local irreducible] Paper6SourceSize.sourceInitialPrecision selectedStartup

open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6R32RootGeneratedRegistryInputs
open J6R14ZeroMode J1PPrinted J6R14LayoutCost J6R36SharedGateway J6R52FreshShape

/-- The same physical count operation, started at the literal padded
source precision with extension length one. The numeric fit is proved from the source. -/
def runAtLiteralSourcePrecision
    (A : RawStartup F order h d j r c e P₀ 1 kp)
    (groups : ActualPhysicalStartupPlan (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit)
    (bytes : (canonicalTable ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree)+1)).result=
    OldOrderedBytes ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree))
      (full_probe_fit ((freshFieldResult F order).f.natDegree))) : Meter (A1R10.Word (printedAnswerWidth NW P₀)) :=
  runFreshPhysicallyRetainedCount (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes

theorem literal_source_startup_emits_the_padded_source_ordinal
    (A : RawStartup F order h d j r c e P₀ 1 kp) :
    (initialPaidWords (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit).result.baseWord.val =
      Fintype.card (Paper6SourceSize.PaddedVariable F order (constantRootWord NW)) + 1 := by
  exact (made_fresh_words_has_actual_base_and_numeric_code NW n P₀
    (fresh_source_native_fits F order) P₀Fit A.mark).2.1.trans
    (Paper6SourceSize.sourceInitialPrecision_eq F order (constantRootWord NW))

/-- Model count and measured clock for the same run whose actual startup
emits the literal source ordinal. -/
theorem literal_source_run_counts_and_pays_the_same_clock
    (A : RawStartup F order h d j r c e P₀ 1 kp)
    (groups : ActualPhysicalStartupPlan (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit)
    (bytes : (canonicalTable ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree)+1)).result=
    OldOrderedBytes ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree))
      (full_probe_fit ((freshFieldResult F order).f.natDegree)))
    (prepCap rootCap : ℕ)
    (data : FreshSourcePreparationAndRoots (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes prepCap rootCap) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit) := selectedStartup (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit
    let D := boot.result.compiled
    let frame := D.frame
    let fd := (freshFieldResult F order).f.natDegree
    let p := J6SourcePrecision.printed NW P₀
    let out := runAtLiteralSourcePrecision (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (kp:=kp) A groups bytes
    let caps := phaseCapsOnTheFreshOriginalInputs (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes prepCap rootCap data
    let slots := actualReceiptSlotRoof (m:=NW) (native:=n) (tc:=centreWidth NW) (tj:=sampleWidth NW)
      (tw:=magnitudeWidth NW) (f:=(freshFieldResult F order).f) (base:=P₀) (ell:=1)
      (literalFreshGroupRoof (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes caps)
    let pads := (exactPadOrder NW (K NW) (printedHalf NW) (constantRootWord NW)).length
    let site := rootSiteFee fd NW (literalDegree NW n) 1 p frame.hp+(literalDegree NW n+1)*slots
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps≤boot.steps+(stablePadBudget (a NW) (K NW) (printedHalf NW) (printedRankWidth NW)+
        legalRootBudget p (printedFactorWidth NW (nSubdiv Graph)) (printedAnswerWidth NW P₀)
           1 frame.words.length (printedRankWidth NW-a NW+13*a NW) NW pads+8+
            gatheredOracleFee NW frame.words.length 1 p site)+5 := by
  exact literal_fresh_exact_count_with_its_actual_phase_tariffs (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes
    (phaseCapsOnTheFreshOriginalInputs (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=P₀) (ell:=1) (kp:=kp) A P₀Fit groups bytes prepCap rootCap data)
    (Paper6SourceSize.sourceInitialPrecision_pos F order)

#print axioms runAtLiteralSourcePrecision
#print axioms literal_source_startup_emits_the_padded_source_ordinal
#print axioms literal_source_run_counts_and_pays_the_same_clock
end
end J6R114PrescribedReceipts
