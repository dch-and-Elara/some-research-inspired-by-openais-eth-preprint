import OuterNodePacking
import J7SourceLabels
import J8SourceMomentKernel

/-!
J8 physical compilation at t = L-1. A port is real precisely because it
has an original incidence; both ends share one packet slot. Endpoint
seating in a graph matching and the source packet orientation law are the
inputs. The at-most-one local hit, absence of pin hits, locality across
children and eligible target witness are conclusions, not fields.
-/

namespace J8Physical

open scoped BigOperators Classical

noncomputable section

abbrev Slot (Packet : Type*) (L : ℕ) := Packet × Fin L
abbrev Wire (Row : Type*) := Row × Bool
abbrev ColPort (Pin : Type*) {V : Type*} (P : V → Type*) := Pin ⊕ (Σ v, P v)

/-- Packet seat and the two indexed descriptions of the same physical
wire. The coordinate-zero label pair swaps its orientation on odd slots. -/
structure Layout (Packet Row Pin V G : Type*) (P : V → Type*) (L : ℕ) where
  seat : Wire Row ↪ Slot Packet L
  column : Wire Row ≃ ColPort Pin P
  rowLabel : Row → G
  pinLabel : Pin → G
  colLabel : V → G
  packetLabels : Packet → G × G
  rowOrientation : ∀ w,
    rowLabel w.1 = if (seat w).2.val % 2 = 0 then (packetLabels (seat w).1).1
      else (packetLabels (seat w).1).2
  columnOrientation : ∀ w,
    Sum.elim pinLabel (fun p : Sigma P => colLabel p.1) (column w) =
      if (seat w).2.val % 2 = 0 then (packetLabels (seat w).1).2
      else (packetLabels (seat w).1).1

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def colOwner (w : Wire R) : S ⊕ V :=
  Sum.map id Sigma.fst (d.column w)

def actualColLabel (w : Wire R) : G :=
  Sum.elim d.pinLabel (fun p : Sigma P => d.colLabel p.1) (d.column w)

def pinWire (pin : S) : Wire R := d.column.symm (Sum.inl pin)

@[simp] theorem pinWire_column (pin : S) : d.column (pinWire d pin) = Sum.inl pin :=
  d.column.apply_symm_apply _

theorem pinWire_colLabel (pin : S) : actualColLabel d (pinWire d pin) = d.pinLabel pin := by
  simp [actualColLabel]

/-- Endpoint seats come from a subset of original edges which is a
matching on both sides, and contains no pin incidences. -/
structure EndpointSeating where
  edges : Set (Wire R)
  chosen : ∀ w, (d.seat w).2.val = 0 ∨ (d.seat w).2.val = L-1 → w ∈ edges
  rowMatching : edges.InjOn Prod.fst
  columnMatching : edges.InjOn (colOwner d)
  nonpin : ∀ w ∈ edges, ∃ v : Sigma P, d.column w = Sum.inr v

/-- Physical outer warp: same packet, two real ports, no modular wrap. -/
def Shift (x y : Wire R) : Prop :=
  (d.seat x).1 = (d.seat y).1 ∧
  ((d.seat x).2.val : ℤ) + ((L : ℤ)-1) = ((d.seat y).2.val : ℤ)

theorem shift_boundaries {x y : Wire R} (h : Shift d x y) :
    (d.seat x).2.val = 0 ∧ (d.seat y).2.val = L-1 :=
  OuterNodePacking.outer_pair_is_boundary _ _ h.2

/-- Matching seats imply at most one actually reached leg at a given
subdivision vertex, even when the two legs lie in different packets. -/
theorem row_hit_unique (e : EndpointSeating d) {x x' y y' : Wire R}
    (h : Shift d x y) (h' : Shift d x' y') (owner : x.1 = x'.1) : x = x' :=
  e.rowMatching (e.chosen x (Or.inl (shift_boundaries d h).1))
    (e.chosen x' (Or.inl (shift_boundaries d h').1)) owner

theorem column_hit_unique (e : EndpointSeating d) {x x' y y' : Wire R}
    (h : Shift d x y) (h' : Shift d x' y')
    (owner : colOwner d y = colOwner d y') : y = y' :=
  e.columnMatching (e.chosen y (Or.inr (shift_boundaries d h).2))
    (e.chosen y' (Or.inr (shift_boundaries d h').2)) owner

theorem successor_unique {x y z : Wire R} (h : Shift d x y) (k : Shift d x z) : y = z := by
  apply d.seat.injective
  apply Prod.ext (h.1.symm.trans k.1)
  apply Fin.ext
  rw [(shift_boundaries d h).2, (shift_boundaries d k).2]

theorem predecessor_unique {x y z : Wire R} (h : Shift d x z) (k : Shift d y z) : x = y := by
  apply d.seat.injective
  apply Prod.ext (h.1.trans k.1.symm)
  apply Fin.ext
  rw [(shift_boundaries d h).1, (shift_boundaries d k).1]

theorem hit_is_nonpin (e : EndpointSeating d) {x y : Wire R} (h : Shift d x y) :
    ∃ v : Sigma P, d.column y = Sum.inr v :=
  e.nonpin y (e.chosen y (Or.inr (shift_boundaries d h).2))

theorem shift_reads_no_pins (e : EndpointSeating d) (p : S) (x : Wire R) :
    ¬ Shift d x (pinWire d p) := by
  intro h
  obtain ⟨q,hq⟩ := hit_is_nonpin d e h
  rw [pinWire_column] at hq
  cases hq

/-- A local surviving pair inherits one common group from the opposite
endpoint parities. This proves local (rather than crossing) wiring at
the zero probe of the extreme odd node. -/
theorem shift_stays_in_child (even : Even L) {x y : Wire R} (h : Shift d x y) :
    d.rowLabel x.1 = actualColLabel d y := by
  have h0 := (shift_boundaries d h).1
  have h1 := (shift_boundaries d h).2
  have hL : 0 < L := (d.seat y).2.isLt.pos
  have parity : (L-1)%2 = 1 := by
    obtain ⟨k,hk⟩ := even
    omega
  rw [d.rowOrientation, actualColLabel, d.columnOrientation, h0, h1, parity, h.1]
  simp

variable [Fintype R] [DecidableEq Packet] [DecidableEq G]

/-- Real targets for the tile of a particular physical column. Nonexistent
padding wires never enter this finite set. -/
def targets (y : Wire R) : Finset (Wire R) :=
  Finset.univ.filter fun x =>
    (d.seat x).1 = (d.seat y).1 ∧
    (d.seat x).2.val % 2 = (d.seat y).2.val % 2 ∧
    d.rowLabel x.1 ≠ actualColLabel d y

theorem target_has_one_target_group {y x x' : Wire R}
    (hx : x ∈ targets d y) (hx' : x' ∈ targets d y) :
    d.rowLabel x.1 = d.rowLabel x'.1 := by
  obtain ⟨hp,hq,_⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hp',hq',_⟩ := (Finset.mem_filter.mp hx').2
  rw [d.rowOrientation x, d.rowOrientation x', hp, hp', hq, hq']

/-- The actual pin wire supplies a target row at the identical slot.
Nonemptiness needs the off-diagonal labeling, not any existence axiom
for a separate candidate row. -/
theorem pinWire_is_target (p : S) (off : d.rowLabel (pinWire d p).1 ≠ d.pinLabel p) :
    pinWire d p ∈ targets d (pinWire d p) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl, ?_⟩
  rw [pinWire_colLabel]
  exact off

theorem pin_targets_nonempty (p : S) (off : d.rowLabel (pinWire d p).1 ≠ d.pinLabel p) :
    (targets d (pinWire d p)).Nonempty :=
  ⟨_, pinWire_is_target d p off⟩

theorem every_target_positive_odd_denom (even : Even L) (size : 2 < L)
    {x y : Wire R} (hx : x ∈ targets d y) :
    0 < (L:ℤ) - 1 - ((d.seat y).2.val % 2 : ℕ) + (d.seat x).2.val ∧
      Odd ((L:ℤ) - 1 - ((d.seat y).2.val % 2 : ℕ) + (d.seat x).2.val) :=
  J8SourceMoment.outer_crossing_denom L _ _ size even (Nat.mod_lt _ (by decide))
    (Finset.mem_filter.mp hx).2.2.1

/-- Apply the old J7 offset law on the actual pin wire. Compatibility
identifies the layout's ordered symbols with the previously constructed
label pair; off-diagonality is proved from the nonzero offset. -/
theorem pin_target_from_source_offset
    {Pair OldRow OldCol OldWire : Type*} [AddCommGroup G]
    (row : OldWire → OldRow) (col : OldWire → J7SourceLabels.OrdinaryColumn Pair OldCol)
    (draw : J7SourceLabels.Block Pair OldRow OldCol → J7SourceLabels.Draw G)
    (p : S) (ed : Pair) (side : Fin 2)
    (same :
      (d.rowLabel (pinWire d p).1, d.pinLabel p) =
      J7SourceLabels.cell row col draw (Sum.inl ((ed,side),false)))
    (nonzero : (draw (Sum.inl ed)).avoidOffset side ≠ 0) :
    (targets d (pinWire d p)).Nonempty := by
  apply pin_targets_nonempty d p
  have off := J7SourceLabels.pin_is_off_diagonal row col draw ed side nonzero
  rw [← same] at off
  exact off

#print axioms row_hit_unique
#print axioms column_hit_unique
#print axioms shift_reads_no_pins
#print axioms shift_stays_in_child
#print axioms target_has_one_target_group
#print axioms pin_target_from_source_offset
#print axioms every_target_positive_odd_denom

end
end J8Physical
