import J9EndFactors

/-! Source moment on the entire physical tile, split into its actual pin
and nonpin occurrences, without a separate coordinate-identification axiom. -/

namespace J9End
open scoped BigOperators Classical
open J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
variable [Fintype S] [Fintype V] [∀ v, Fintype (P v)]
variable (d : J8Physical.Layout Packet R S V G P L)

def tileSplit (a : S) : Tile d a ≃ PinTile d a ⊕ OldTile d a :=
  (d.column.subtypeEquivOfSubtype' (p := fun w => SameTile d w (pinWire d a))).trans
    Equiv.subtypeSum

omit [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G] [Fintype S] [Fintype V] [(v : V) → Fintype (P v)] in
theorem tileSplit_pin (a : S) (p : PinTile d a) :
    ((tileSplit d a).symm (Sum.inl p)).val = pinWire d p.1 := rfl

omit [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G] [Fintype S] [Fintype V] [(v : V) → Fintype (P v)] in
theorem tileSplit_old (a : S) (p : OldTile d a) :
    ((tileSplit d a).symm (Sum.inr p)).val = ordinaryWire d p.1 := rfl

omit [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G] [Fintype S] [Fintype V] [(v : V) → Fintype (P v)] in
theorem chart_ordinal_exact (a : S) (w : Tile d a) :
    ((slot d w.1).val - (slot d (pinWire d a)).val % 2) / 2 =
      ordinal d w.1 := by
  have h := w.2.2
  unfold slot ordinal
  omega

omit [DecidableEq R] [Fintype Packet] in
theorem chart_moment_pin_old (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b : ℕ) (x : Fin M → Bool) :
    J9FactorBounds.moment (chart d a idx truth) b x =
      ((∑ p : PinTile d a, (ordinal d (pinWire d p.1))^b *
          (if x (idx (pinWire d p.1)) then 1 else 0)) +
        ∑ v : OldTile d a, (ordinal d (ordinaryWire d v.1))^b *
          (if x (idx (ordinaryWire d v.1)) then 1 else 0) : ℕ) := by
  let f (w : Tile d a) : ℕ := (ordinal d w.1)^b * (if x (idx w.1) then 1 else 0)
  unfold J9FactorBounds.moment NativeBitBudget.tileMoment
  have h1 : (∑ w : Tile d a,
      ((((chart d a idx truth).tileSlot w).val - (chart d a idx truth).tau.val)/2) ^ b *
        (if x ((chart d a idx truth).tileInput w) then 1 else 0)) = ∑ w, f w := by
    apply Finset.sum_congr rfl
    intro w hw
    change (((slot d w.1).val - (slot d (pinWire d a)).val % 2)/2)^b * _ = _
    rw [chart_ordinal_exact d a w]
    rfl
  have he : (∑ w : Tile d a, f w) =
      ∑ q : PinTile d a ⊕ OldTile d a, f ((tileSplit d a).symm q) :=
    Fintype.sum_equiv (tileSplit d a) _ _ (fun w => by simp)
  rw [h1, he, Fintype.sum_sum_type]
  simp [f, tileSplit_pin, tileSplit_old]

#print axioms chart_moment_pin_old
end
end J9End

