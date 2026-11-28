import J6R117HeldPhysicalImage
import J6R112ExecutedSelectedStartupBase
import J6R112GuardedInputBindingBase
import J6R116PhysicalRetainedChartImage

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
open J6R117HeldPhysicalImage J6R52FreshShape J6R111KeptOwnerFlow J6R33StatefulArithmeticPage

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
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
local notation "s" => (physicalSize m n)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp) (fit : base ≤ physicalSize (nWires (guardedInOrder F order.roster))
    (Paper6SourceSize.sourceNativeSize F order)^2)

abbrev ActualPhysicalStartupPlan :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let startup : Meter (StartupImage A fit) :=
    selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  let image := startup.result
  PhysicalRetainedImagePlan image

section HeldSource
local notation "Image" => (selectedStartup A fit).result
local instance freshHeldIrreducible :
    Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
  ⟨(generated_fresh_field_is_permitted F order).2⟩

/-- Prepare against the real startup image, consuming its returned admission.
The suppliers have the original held-data types at the literal source schedule. -/
def freshPhysicalPlanFromHeldSource
    (pad : ℕ)
    (prior : PageBank (freshFieldResult F order).f ell
      (KeyWidth kp (centreWidth m) (sampleWidth m)) (chosenPrec m) (magnitudeWidth m)
      (chosenBW m) (pageKeyWidth m+pad))
    (synced : prior.synced)
    (reserved : ∀ header∈prior.headers,header.id.bits.take kp≠(Image).compiled.mark.bits)
    (held : ∀ i j g, HeldConfigurationAt (Image) pad i j g) :
    ActualPhysicalStartupPlan A fit :=
  useTheActualHeldConfiguration (Image) pad prior synced reserved held
end HeldSource

variable (groups : ActualPhysicalStartupPlan A fit)
local notation "fieldDegree" => ((freshFieldResult F order).f.natDegree)
variable (bytes : (canonicalTable ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree)+1)).result=
    OldOrderedBytes ((freshFieldResult F order).f.natDegree)
      (fullProbeDegree ((freshFieldResult F order).f.natDegree))
      (full_probe_fit ((freshFieldResult F order).f.natDegree)))

theorem fresh_posted_and_mounted_payload_has_literal_source_scale
    (i : J6Recovery.Addr m) (j : Fin (J6R14ZeroMode.literalDegree m n+1)) (g : Fin 64) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let image := (selectedStartup A fit).result
    let P := mountTheChartOnEveryChosenActualGroup image groups bytes
    let W := chooseWidths m n (fresh_source_native_fits F order)
    let row := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables P.pad P.prior P.sync P.reserved i j g row rfl
    let actual := (P.acquire i j g row rfl posted.result).result
    actual.size=physicalSize m (Paper6SourceSize.sourceNativeSize F order) ∧
      actual.constant=2 ∧ HEq actual.selector
        ((freshSearchedRootShape F order base A.three A.large).selector ell) := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  exact posted_and_mounted_payload_has_source_scale (selectedStartup A fit).result groups bytes i j g

def runFreshPhysicallyRetainedCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  let out := runPhysicalRetainedCountAtImage boot.result (mountTheChartOnEveryChosenActualGroup boot.result groups bytes)
  ⟨out.result,boot.steps+out.steps+5⟩


theorem fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
    (positiveBase : 0<base) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
    let count := runPhysicalRetainedCountAtImage boot.result (mountTheChartOnEveryChosenActualGroup boot.result groups bytes)
    bitsValue (runFreshPhysicallyRetainedCount A fit groups bytes).result.val=PinnedCNF.modelCount F ∧
      (runFreshPhysicallyRetainedCount A fit groups bytes).steps=boot.steps+count.steps+5 := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  obtain ⟨zero,count⟩ := ordered_original_input_supplies_its_own_count_and_opening F order
  exact ⟨the_same_ready_physical_image_returns_the_guarded_count boot.result
    (mountTheChartOnEveryChosenActualGroup boot.result groups bytes) positiveBase zero (PinnedCNF.modelCount F) count,rfl⟩

#print axioms freshPhysicalPlanFromHeldSource
#print axioms fresh_posted_and_mounted_payload_has_literal_source_scale
#print axioms runFreshPhysicallyRetainedCount
#print axioms fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
end
end J6R114PrescribedReceipts

