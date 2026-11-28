import J8PhysicalRecovery
import J9FactorBoundsMesh

/-! Real outer-row and tile incidence witnesses for the unsigned part
of J9's centered-lift certificate. No asserted tile or hit bounds. -/

namespace J9End
open scoped BigOperators Classical
noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
variable (d : J8Physical.Layout Packet R S V G P L)

abbrev Wire := J8Physical.Wire R
abbrev Tile (a : S) := {w : J8Physical.Wire R // J8Physical.SameTile d w (J8Physical.pinWire d a)}

def hit (w : J8Physical.Wire R) : Bool := decide (∃ y, J8Physical.Shift d w y)

omit [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G] in
theorem hit_true_iff (w : J8Physical.Wire R) :
    hit d w = true ↔ ∃ y, J8Physical.Shift d w y := by simp [hit]

def hitDestination (a : S) (w : J8Physical.Wire R) : J8Physical.Wire R :=
  if h : ∃ y, J8Physical.Shift d w y then Classical.choose h else J8Physical.pinWire d a

omit [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G] in
theorem hitDestination_spec (a : S) {w y : J8Physical.Wire R} (h : J8Physical.Shift d w y) :
    hitDestination d a w = y := by
  unfold hitDestination
  rw [dif_pos (show ∃ y, J8Physical.Shift d w y from ⟨y,h⟩)]
  exact J8Physical.successor_unique d (Classical.choose_spec _) h

def slot (w : J8Physical.Wire R) : Fin L := (d.seat w).2

def targetSlots (a : S) : Finset (Fin L) :=
  (J8Physical.targets d (J8Physical.pinWire d a)).image (slot d)

omit [DecidableEq R] [Fintype Packet] in
theorem targetSlot_injective (a : S) :
    Set.InjOn (slot d) ↑(J8Physical.targets d (J8Physical.pinWire d a)) := by
  intro x hx y hy h
  have hx' := (Finset.mem_filter.mp hx).2.1
  have hy' := (Finset.mem_filter.mp hy).2.1
  exact d.seat.injective (Prod.ext (hx'.trans hy'.symm) h)

def targetWire (a : S) (i : Fin L) : J8Physical.Wire R :=
  if h : ∃ w ∈ J8Physical.targets d (J8Physical.pinWire d a), slot d w = i
  then Classical.choose h else J8Physical.pinWire d a

omit [DecidableEq R] [Fintype Packet] in
theorem targetWire_spec (a : S) {i : Fin L} (hi : i ∈ targetSlots d a) :
    targetWire d a i ∈ J8Physical.targets d (J8Physical.pinWire d a) ∧
      slot d (targetWire d a i) = i := by
  have h := Finset.mem_image.mp hi
  unfold targetWire
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Every coefficient address corresponds to a real packet position;
the branch of targetWire outside the target set is never used. -/
def chart (a : S) (idx : J8Physical.Wire R ≃ Fin M) (truth : (Fin M → Bool) → Bool) :
    J9FactorBounds.Chart L M R (Tile d a) where
  hit := fun r b => hit d (r,b)
  rowInput := fun r b => idx (hitDestination d a (r,b))
  table := truth
  tileSlot := fun w => slot d w.1
  tileInput := fun w => idx w.1
  rowOf := fun i => (targetWire d a i).1
  leg := fun i => (targetWire d a i).2
  targets := targetSlots d a
  tau := ⟨(slot d (J8Physical.pinWire d a)).val % 2, Nat.mod_lt _ (by decide)⟩

omit [DecidableEq R] [Fintype Packet] in
theorem chart_parity (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) :
    ∀ i ∈ (chart d a idx truth).targets, i.val%2 = (chart d a idx truth).tau.val := by
  intro i hi
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hi
  exact (Finset.mem_filter.mp hw).2.2.1

omit [DecidableEq R] [Fintype Packet] in
theorem chart_tile_injective (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) : Function.Injective (chart d a idx truth).tileSlot := by
  intro x y h
  apply Subtype.ext
  apply d.seat.injective
  exact Prod.ext (x.2.1.trans y.2.1.symm) h

omit [DecidableEq R] [Fintype Packet] in
theorem chart_one_hit (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (e : J8Physical.EndpointSeating d) :
    ∀ r, ¬ ((chart d a idx truth).hit r false = true ∧
      (chart d a idx truth).hit r true = true) := by
  intro r h
  obtain ⟨y,hy⟩ := (hit_true_iff d (r,false)).mp h.1
  obtain ⟨z,hz⟩ := (hit_true_iff d (r,true)).mp h.2
  have bad := J8Physical.row_hit_unique d e hy hz rfl
  exact Bool.false_ne_true (congrArg Prod.snd bad)

omit [DecidableEq R] in
theorem chart_active_rows_le_packets (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) :
    (J9FactorBounds.activeRows (chart d a idx truth)).card ≤ Fintype.card Packet := by
  let g := chart d a idx truth
  let active := J9FactorBounds.activeRows g
  have origin : ∀ r ∈ active, ∃ b : Bool, ∃ y, J8Physical.Shift d (r,b) y := by
    intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    change (hit d (r,false) || hit d (r,true)) = true at hh
    rcases Bool.or_eq_true_iff.mp hh with hl | hr
    · exact ⟨false, (hit_true_iff d _).mp hl⟩
    · exact ⟨true, (hit_true_iff d _).mp hr⟩
  let leg (r : ↥active) : Bool := Classical.choose (origin r.1 r.2)
  let packet (r : ↥active) : Packet := (d.seat (r.1,leg r)).1
  have inj : Function.Injective packet := by
    intro r r' he
    obtain ⟨y,hy⟩ := Classical.choose_spec (origin r.1 r.2)
    obtain ⟨y',hy'⟩ := Classical.choose_spec (origin r'.1 r'.2)
    have h0 := (J8Physical.shift_boundaries d hy).1
    have h1 := (J8Physical.shift_boundaries d hy').1
    have hw : (r.1, leg r) = (r'.1, leg r') := d.seat.injective
      (Prod.ext he (Fin.ext (h0.trans h1.symm)))
    exact Subtype.ext (congrArg Prod.fst hw)
  simpa [active,g] using Fintype.card_le_of_injective packet inj

omit [DecidableEq R] in
theorem chart_active_rows_budget (a : S) (idx : J8Physical.Wire R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (capacity : L * Fintype.card Packet ≤ 3*M) :
    L * (J9FactorBounds.activeRows (chart d a idx truth)).card ≤ 3*M :=
  (Nat.mul_le_mul_left L (chart_active_rows_le_packets d a idx truth)).trans capacity

#print axioms chart_parity
#print axioms chart_tile_injective
#print axioms chart_one_hit
#print axioms chart_active_rows_budget

end
end J9End

