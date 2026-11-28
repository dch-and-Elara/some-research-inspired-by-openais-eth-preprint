import J6R52FreshShapeDimension
import J6R52FreshShapeField

/-! Discharge the fresh numeric threshold from the actual old printed
guard, and certify that the field compiler's deterministic lower bits
did not change merely because a different graph chart was selected.
This assertion concerns field bits, not row, seat, or tile bytes. -/
namespace J6R52FreshShape
open scoped Classical Polynomial
open Polynomial Std.Sat J6Mesh J7R10Plant A1R10
open J6R28GeneratedRootFrame J6R24LegalLayout J6R29BinaryFieldSearch
open J6R26StablePreparedRoot J6R51Ingress J1PPrinted
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 14000000

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {F : CNF V} {base : ℕ} (order : DeclaredOrder V)
local notation "H" => (guardedInOrder F order.roster)
local notation "m" => (nWires H)
local notation "n" => (Paper6SourceSize.sourceNativeSize F order)

theorem fresh_large_from_printed_guard (G : PrintedRootGuard F base) :
    printedGuard m n := by
  show (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m (sourceNative H))
  rw [fresh_literal_physical_size_exact F order]
  exact G.large

def freshShapeFromOriginalGuard (G : PrintedRootGuard F base) :
    RootShape (freshFieldResult F order).f m (printedHalf m) base n (printedRankWidth m)
      (freshPlant H (guardRoster order)) (constantRootWord m) :=
  freshSearchedRootShape F order base G.three (fresh_large_from_printed_guard order G)

theorem accepted_field_bits_congr (a b : ℕ) (ha : 0<a) (hb : 0<b) (eq : a=b) :
    (acceptedField a ha).result.val=(acceptedField b hb).result.val := by
  subst b
  rfl

theorem original_fresh_field_bytes_same (G : PrintedRootGuard F base) :
    (freshFieldResult F order).lower.val=(generatedField G).result.lower.val := by
  change (acceptedField (printedFieldWidth m n)
      (printed_field_width_positive m n (fresh_source_native_fits F order))).result.val =
    (acceptedField (printedFieldWidth (J7R10Readout.mCNF F) (literalNativeSize F))
      (printed_field_width_positive _ _ (literal_native_fits F G.three))).result.val
  apply accepted_field_bits_congr
  change 4*Nat.clog 2 (physicalSize m (sourceNative H)) =
    4*Nat.clog 2 (physicalSize (J7R10Readout.mCNF F) (literalNativeSize F))
  rw [fresh_literal_physical_size_exact F order]

#print axioms fresh_large_from_printed_guard
#print axioms freshShapeFromOriginalGuard
#print axioms accepted_field_bits_congr
#print axioms original_fresh_field_bytes_same
end
end J6R52FreshShape
