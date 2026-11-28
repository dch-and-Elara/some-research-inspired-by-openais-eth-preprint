import J7R43LiteralMass

/-! Exact sign readout from the unreduced individual source integers.
No division in the finite residue ring is involved; the distinct
actual pin coordinates are used in rational Vandermonde decoding. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open J8Physical J8J9Grouped NativeMomentReconstruction
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L) (hL : 0<L)
variable (F : OldTables d) (sign : S→Bool)

include hL in
theorem decode_literal_integer_tile (s : S)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x = true) :
    NativeMomentReconstruction.decodeBits (coordinates d s)
      (fun _ => (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : ℚ))
      (fun b => actualPublicMoment d e even F s b.val)
      (fun b => (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : ℚ)) =
        fun j => sign (pinEnumeration d s j).val := by
  let Z : ℚ := pinnedChildMass d e even F (d.pinLabel s)
  let σ : Fin (Fintype.card (PinTile d s)) → Bool := fun j => sign (pinEnumeration d s j).val
  let obs : Fin (Fintype.card (PinTile d s)) → ℚ := fun b =>
    (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : ℚ)
  let background : Fin (Fintype.card (PinTile d s)) → ℚ :=
    fun b => actualPublicMoment d e even F s b.val
  rw [show (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : ℚ) = Z
    from actual_baseline_mass_formula d e even hL F sign _]
  have massPositive : 0<Z := all_local_mass_positive d e even hL F _ sat
  have exactFrac : decode (coordinates d s) (fun _ => Z) background obs =
      fun j => bitValue (σ j) := by
    apply NativeMomentReconstruction.decode_scaled _ _ _ _ _ (coordinates_injective d s)
      (fun _ => massPositive.ne')
    intro b
    exact actual_source_mass_formula d e even hL F sign s b sat
  change decodeBits (coordinates d s) (fun _ => Z) background obs = σ
  funext j
  unfold decodeBits
  rw [exactFrac]
  cases h : σ j <;> simp [h,bitValue]

/-- The count of the real requests is exactly the number of moments;
the actual set of all source tiles is handled by the existing atlas
partition, not by padding unused holes with more questions. -/
theorem per_tile_request_count (s : S) :
    Fintype.card (Fin (Fintype.card (PinTile d s))) = Fintype.card (PinTile d s) := by simp

#print axioms decode_literal_integer_tile
#print axioms per_tile_request_count
end
end J7R43Literal