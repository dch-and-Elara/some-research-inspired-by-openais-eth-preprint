import J6R112ExecutedSelectedStartupBase
import J6R112GuardedInputBindingBase
import J6R115AdmittedExecutionImage

/-! The physically selected startup and the physically selected outer
count run in succession. The proof-side raw comparator is not a step
in the new execution. -/
namespace J6R114PrescribedReceipts
open J6R112ExecutedSelectedStartup J6R112GuardedInputBinding AOracleMachineTimeTape
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
set_option maxHeartbeats 2500000
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

abbrev AdmittedPlanOnStartup :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let startup : Meter (StartupImage A fit) :=
    selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  let image := startup.result
  AdmittedExecutionImage image

variable (groups : AdmittedPlanOnStartup A fit)

def runFreshAdmittedCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  let out := exactCountFromKeptAdmissions boot.result groups
  ⟨out.result,boot.steps+out.steps+5⟩


theorem fresh_admitted_execution_counts_the_submitted_CNF_and_uses_its_own_clock
    (positiveBase : 0<base) :
    letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
      ⟨(generated_fresh_field_is_permitted F order).2⟩
    let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
    let count := exactCountFromKeptAdmissions boot.result groups
    bitsValue (runFreshAdmittedCount A fit groups).result.val=PinnedCNF.modelCount F ∧
      (runFreshAdmittedCount A fit groups).steps=boot.steps+count.steps+5 := by
  letI : Fact (Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f)) :=
    ⟨(generated_fresh_field_is_permitted F order).2⟩
  let boot : Meter (StartupImage A fit) := selectedStartup (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e) (base:=base) (ell:=ell) (kp:=kp) A fit
  obtain ⟨zero,count⟩ := ordered_original_input_supplies_its_own_count_and_opening F order
  exact ⟨count_with_one_actual_admission_at_every_address boot.result groups positiveBase zero (PinnedCNF.modelCount F) count,rfl⟩

#print axioms runFreshAdmittedCount
#print axioms fresh_admitted_execution_counts_the_submitted_CNF_and_uses_its_own_clock
end
end J6R114PrescribedReceipts

