import J6R52FreshShapeCore
import J6R28GeneratedRootFrameWidth

/-! Source size and initial precision for the literal padded J6 instance. -/
namespace Paper6SourceSize

open Std.Sat J6Mesh J6R51Ingress J7R10Plant
open J6R24LegalLayout J6R28GeneratedRootFrame

set_option autoImplicit false

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (order : DeclaredOrder V)

local notation "H" => guardedInOrder F order.roster
local notation "m" => nWires H

/-- Count declared variables and guarded clauses before replication. -/
def sourceNativeSize : ℕ :=
  Fintype.card (Option V) + (List.length H)

/-- The source size is bounded by the number of physical half-edges. -/
theorem sourceNativeSize_le_wires [Nonempty V] (three : ∀ row ∈ F, row.length ≤ 3) :
    sourceNativeSize F order ≤ m :=
  J6R52FreshShape.source_native_fits F order three

/-- Each pad label is one actual negative-unary gadget. -/
abbrev SourcePad (w : Fin (a m) → Fin 64) :=
  J6OrientedHost.Pad w m (K m) (printedHalf m)

/-- Variables have a copy index or a distinct padding gadget label. -/
abbrev PaddedVariable (w : Fin (a m) → Fin 64) :=
  (Fin (L m) × Option V) ⊕ SourcePad F order w

/-- The disjoint CNF copies followed by the negative unary clause of each actual pad. -/
def paddedFormula (w : Fin (a m) → Fin 64) : CNF (PaddedVariable F order w) :=
  (List.finRange (L m)).flatMap
    (fun copy => List.map (fun row => row.map (fun lit => (.inl (copy, lit.1), lit.2))) H) ++
  (Finset.univ : Finset (SourcePad F order w)).toList.map
    (fun pad => [(.inr pad, false)])

theorem sourcePad_card (w : Fin (a m) → Fin 64) :
    Fintype.card (SourcePad F order w) = literalPadCount m := by
  have layout := Fintype.card_congr (J6PhysicalPacking.placement
    (J6RecursiveOrientation.diagonal w) m (K m) (printedHalf m) (printed_room m))
  simp only [J6PhysicalPacking.Wire, J6PhysicalPacking.Slot,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at layout
  change m * (2 * printedHalf m) + Fintype.card (SourcePad F order w) * 2 =
    Fintype.card (CellType (a m)) * (K m * (2 * printedHalf m)) at layout
  rw [printed_half_correct, literal_cell_card, mesh_product] at layout
  have wires := literal_pad_count_source m
  omega

theorem paddedVariable_card (w : Fin (a m) → Fin 64) :
    Fintype.card (PaddedVariable F order w) =
      L m * Fintype.card (Option V) + literalPadCount m := by
  simp only [PaddedVariable, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, sourcePad_card F order w]

theorem paddedFormula_length (w : Fin (a m) → Fin 64) :
    (paddedFormula F order w).length = L m * (List.length H) + literalPadCount m := by
  simp only [paddedFormula, List.length_append, List.length_flatMap, List.length_map,
    List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul, Nat.cast_id,
    Finset.length_toList, Finset.card_univ, sourcePad_card F order w]

/-- The size parameter for the padded source schedule. -/
def sourcePaddedSize : ℕ :=
  physicalSize m (sourceNativeSize F order)

theorem padded_size_eq (w : Fin (a m) → Fin 64) :
    Fintype.card (PaddedVariable F order w) + (paddedFormula F order w).length =
      sourcePaddedSize F order := by
  rw [paddedVariable_card, paddedFormula_length, sourcePaddedSize, physicalSize,
    sourceNativeSize, Nat.mul_add]
  have hp := literal_pad_count_source m
  rw [Nat.mul_comm m (L m)] at hp
  omega

/-- The original sparse source starts at one plus the number of padded variables. -/
def sourceInitialPrecision : ℕ :=
  L m * Fintype.card (Option V) + (M m - L m * m) / 2 + 1

theorem sourceInitialPrecision_eq (w : Fin (a m) → Fin 64) :
    sourceInitialPrecision F order = Fintype.card (PaddedVariable F order w) + 1 := by
  rw [sourceInitialPrecision, paddedVariable_card, literal_pad_count_half,
    Nat.mul_comm m (L m)]

theorem sourceInitialPrecision_pos : 0 < sourceInitialPrecision F order := by
  unfold sourceInitialPrecision
  omega

theorem sourceInitialPrecision_le_size :
    sourceInitialPrecision F order ≤ sourcePaddedSize F order := by
  have spare := (physicalSize_ceiling m 0 (Nat.zero_le _)).1
  simp only [physicalSize, Nat.mul_zero, Nat.add_zero] at spare
  have powerPositive : 0 < (2 : ℕ) ^ (lambda m - 1) := by positivity
  have gadgetPositive : 1 ≤ (M m - L m * m) / 2 := by omega
  unfold sourceInitialPrecision sourcePaddedSize physicalSize sourceNativeSize
  rw [Nat.mul_add]
  omega

theorem sourceInitialPrecision_le_sq :
    sourceInitialPrecision F order ≤ (sourcePaddedSize F order)^2 := by
  have h := sourceInitialPrecision_le_size F order
  have hp := sourceInitialPrecision_pos F order
  have hs : 1 ≤ sourcePaddedSize F order := by omega
  exact h.trans (by simpa only [Nat.mul_one, pow_two] using
    (Nat.mul_le_mul_left (sourcePaddedSize F order) hs))

theorem sourcePaddedSize_ceiling [Nonempty V] (three : ∀ row ∈ F, row.length ≤ 3) :
    2^(lambda m - 1) < sourcePaddedSize F order ∧ sourcePaddedSize F order ≤ M m ∧
      Nat.clog 2 (sourcePaddedSize F order) = lambda m :=
  physicalSize_ceiling m _ (sourceNativeSize_le_wires F order three)

/-- Transfer only expressions whose size argument is the ceiling logarithm. -/
theorem subdivision_clog_eq [Nonempty V] (three : ∀ row ∈ F, row.length ≤ 3) :
    Nat.clog 2 (physicalSize m (nSubdiv H)) = Nat.clog 2 (sourcePaddedSize F order) :=
  J6R52FreshShape.same_logged_printed_schedule m _ _
    (J6R52FreshShape.subdivision_native_fits H) (sourceNativeSize_le_wires F order three)

#print axioms sourceNativeSize_le_wires
#print axioms sourcePad_card
#print axioms paddedVariable_card
#print axioms paddedFormula_length
#print axioms padded_size_eq
#print axioms sourceInitialPrecision_eq
#print axioms sourceInitialPrecision_pos
#print axioms sourceInitialPrecision_le_size
#print axioms sourceInitialPrecision_le_sq
#print axioms sourcePaddedSize_ceiling
#print axioms subdivision_clog_eq

end
end Paper6SourceSize

