import J6R52FreshShapeField

/-! Expose the all-in-one meter used for a fresh computed RootShape.
It includes the actual field search as well as frame building, rather
than hiding the earlier search in the coefficient provider. -/
namespace J6R52FreshShape
open scoped Classical Polynomial
open Polynomial Std.Sat J6Mesh J7R10Plant AOracleMachineTime
open J6R28GeneratedRootFrame J6R24LegalLayout J6R24MeteredRecursion J6R29BinaryFieldSearch
open J6R10Reachable J6R26StablePreparedRoot J6R51Ingress J6R12Blueprint J6R11Repack J6R12Repack J6ActiveRun
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13500000

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
local notation "H" => (guardedInOrder F order.roster)
local notation "S" => (guardRoster order)
local notation "m" => (nWires H)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)

def paidFreshFieldFrame (base : ℕ) :
    Meter (Frame (freshFieldResult F order).f (J6SourcePrecision.printed m base)) :=
  let A := freshFieldSearch F order
  let R := nativeGeneratedFrame A.result (fresh_source_native_fits F order) base
  ⟨R.result,A.steps+R.steps+7⟩

theorem paid_fresh_field_frame_actual (base : ℕ) :
    let e := printedFieldWidth m n
    let A := paidFreshFieldFrame F order base
    let B := freshFieldFrame F order base
    A.result=B.result ∧
      A.steps=(freshFieldSearch F order).steps+B.steps+7 ∧
      A.steps≤fieldSearchFee e+6+frameBuildFee e (J6SourcePrecision.printed m base)+7 := by
  have r := fresh_searched_frame_receipt F order base
  refine ⟨rfl,rfl,?_⟩
  change (freshFieldSearch F order).steps+(freshFieldFrame F order base).steps+7≤_
  rw [r.2.2.2.2]
  exact Nat.add_le_add_right (Nat.add_le_add_right r.2.1 _) _

theorem generated_fresh_field_is_permitted :
    (freshFieldResult F order).f.Monic ∧
      Irreducible (NativeProbeRing.residuePoly (freshFieldResult F order).f) :=
  ⟨native_field_monic (freshFieldResult F order),(freshFieldResult F order).irreducible⟩

theorem generated_fresh_odd_precision (base : ℕ) (three : ∀ row∈F,row.length≤3)
    (large : printedGuard m n) (ell : ℕ) (i : J6Recovery.Addr m) :
    let R := freshSearchedRootShape F order base three large
    let f := (freshFieldResult F order).f
    registerPrecision (rootParams f ell m n)
      (physicalRootCall f ell base m (printedHalf m) (nSubdiv H) (freshPlant H S) (constantRootWord m))
      (R.centre ell i) = J6SourcePrecision.printed m base := by
  exact (freshSearchedRootShape F order base three large).precision ell i

theorem generated_fresh_root_uses_literal_source_cutoff
    (base ell : ℕ) (three : ∀ row∈F,row.length≤3) (large : printedGuard m n) :
    let f := (freshFieldResult F order).f
    let Ssrc := physicalSize m (Paper6SourceSize.sourceNativeSize F order)
    let R := physicalRootCall f ell base m (printedHalf m) (nSubdiv H) (freshPlant H S) (constantRootWord m)
    (rootParams f ell m n).cutoff = J9PrintedSchedule.leafThreshold Ssrc (Nat.clog 2 Ssrc) ∧
      J9PrintedSchedule.leafThreshold Ssrc (Nat.clog 2 Ssrc) < R.edges := by
  exact ⟨rfl,((freshSearchedRootShape F order base three large).ready ell).active⟩

#print axioms generated_fresh_root_uses_literal_source_cutoff
#print axioms paid_fresh_field_frame_actual
#print axioms generated_fresh_field_is_permitted
#print axioms generated_fresh_odd_precision
end
end J6R52FreshShape
