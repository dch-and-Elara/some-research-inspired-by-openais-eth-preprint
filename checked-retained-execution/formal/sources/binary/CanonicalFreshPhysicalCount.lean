import J6R116FreshPhysicalRetained
import CanonicalChosenInstance

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
local notation "m" => (nWires Graph)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)
variable {h d j r c e base ell kp : ℕ}
variable (A : RawStartup F order h d j r c e base ell kp) (fit : base ≤ physicalSize (nWires (guardedInOrder F order.roster))
    (Paper6SourceSize.sourceNativeSize F order)^2)

open Paper6CanonicalChosenInstance

/-- The binary-order certificate for the field that the corrected
source-size startup actually generates. -/
theorem freshBinaryExactRows :
    (canonicalTable (freshFieldResult F order).f.natDegree
      (fullProbeDegree (freshFieldResult F order).f.natDegree + 1)).result =
    OldOrderedBytes (freshFieldResult F order).f.natDegree
      (fullProbeDegree (freshFieldResult F order).f.natDegree)
      (full_probe_fit (freshFieldResult F order).f.natDegree) := by
  let d := (freshFieldResult F order).f.natDegree
  have pos : 0 < d := by
    change 0 < (freshFieldResult F order).f.natDegree
    rw [native_field_degree]
    exact printed_field_width_positive m n (fresh_source_native_fits F order)
  exact the_paid_table_matches_every_actual_chosen_prefix d (fullProbeDegree d) pos (full_probe_fit d)

variable (groups : ActualPhysicalStartupPlan A fit)

/-- The retained count computation using the corrected startup and
the binary probe order. -/
def runFreshBinaryOrderCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  runFreshPhysicallyRetainedCount A fit groups (freshBinaryExactRows (F:=F) (order:=order))

theorem binary_order_actual_run_counts_the_original_CNF (basePositive : 0<base) :
    bitsValue (runFreshBinaryOrderCount A fit groups).result.val =
      PinnedCNF.modelCount F :=
  (fresh_physical_execution_counts_the_original_CNF_and_pays_actual_startup
    A fit groups (freshBinaryExactRows (F:=F) (order:=order)) basePositive).1

#print axioms freshBinaryExactRows
#print axioms runFreshBinaryOrderCount
#print axioms binary_order_actual_run_counts_the_original_CNF
end

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {order : DeclaredOrder V}
local notation "Graph" => (guardedInOrder F order.roster)
local notation "literalBase" => (Paper6SourceSize.sourceInitialPrecision F order)
omit [Nonempty V] in
private theorem canonicalSourcePrecisionFits (F : CNF V) (order : DeclaredOrder V) :
    Paper6SourceSize.sourceInitialPrecision F order ≤
      physicalSize (nWires (guardedInOrder F order.roster))
        (Paper6SourceSize.sourceNativeSize F order)^2 := by
  simpa only [Paper6SourceSize.sourcePaddedSize] using
    Paper6SourceSize.sourceInitialPrecision_le_sq F order

attribute [local irreducible] Paper6SourceSize.sourceInitialPrecision selectedStartup

variable {h d j r c e kp : ℕ}
theorem binary_order_at_literal_source_precision_counts
    (A : RawStartup F order h d j r c e literalBase 1 kp)
    (groups : ActualPhysicalStartupPlan (F:=F) (order:=order)
      (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e)
      (base:=literalBase) (ell:=1) (kp:=kp) A (canonicalSourcePrecisionFits F order)) :
    bitsValue (runFreshBinaryOrderCount (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e)
      (base:=literalBase) (ell:=1) (kp:=kp) A (canonicalSourcePrecisionFits F order) groups).result.val =
      PinnedCNF.modelCount F := by
  exact binary_order_actual_run_counts_the_original_CNF (F:=F) (order:=order) (h:=h) (d:=d) (j:=j) (r:=r) (c:=c) (e:=e)
      (base:=literalBase) (ell:=1) (kp:=kp) A (canonicalSourcePrecisionFits F order) groups
    (Paper6SourceSize.sourceInitialPrecision_pos F order)

#print axioms binary_order_at_literal_source_precision_counts
end
end J6R114PrescribedReceipts

