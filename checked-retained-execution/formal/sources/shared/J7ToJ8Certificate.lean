import J7ToJ8Layout
import J7SeatRounded

/-! # A seated J7 source is a J8 layout on the same actual wires. -/
open scoped BigOperators Classical

namespace J7ToJ8Certificate
open J7ToJ8Incidence J7ToJ8Layout J7SourceLabels J7SeatPacking J7SeatSource
open J7FullWordAssembly P11FullPacking

noncomputable section
set_option maxHeartbeats 1200000

variable {A Pair Row Col W : Type*} [LinearOrder A] {t b : ℕ}

theorem pin_wire_identifies (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
    (p : Pin Pair) :
    rowWire row two (J8Physical.pinWire (physicalLayout row col two z seat preserves) p) =
      pinEmbed Pair W p := by
  have h := J8Physical.pinWire_column (physicalLayout row col two z seat preserves) p
  change (colWire col).symm
    (rowWire row two (J8Physical.pinWire (physicalLayout row col two z seat preserves) p)) = .inl p at h
  simpa only [Equiv.apply_symm_apply, colWire_pin] using congrArg (colWire col) h

/-- Apply the actual R4 word law to the J8 layout's old pin, not to an
unrelated row/column witness. -/
theorem pin_head_off [Fintype A]
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (hz : ∀ d, 0 < J7FullWordCells.weight d (z d))
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
    (p : Pin Pair) :
    let d := physicalLayout row col two z seat preserves
    d.rowLabel (J8Physical.pinWire d p).1 ≠ d.pinLabel p := by
  dsimp only
  let d := physicalLayout row col two z seat preserves
  let w := J8Physical.pinWire d p
  have h := rowWire_owner row two w
  rw [pin_wire_identifies row col two z seat preserves p] at h
  have hx := layout_owns_pins row col z hz p
  rw [label_head] at hx
  change subdivisionHead z w.1 ≠ pinHead z p
  rw [← h]
  exact hx

/-- The extreme probe has no pin input and its real last-slot columns
have the exact same first-coordinate grouping as the real first-slot
rows; in addition the original pin itself is a real eligible target. -/
theorem compiled_probe [Fintype A] [Fintype Pair] [Fintype Row]
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (hz : ∀ d, 0 < J7FullWordCells.weight d (z d))
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
    (hR : Set.InjOn (rowNode row) {w | isEnd (seat w)})
    (hC : Set.InjOn (colNode col) {w | isEnd (seat w)})
    (hP : ∀ p, ¬ isEnd (seat (pinEmbed Pair W p))) :
    let d := physicalLayout row col two z seat preserves
    (∀ p (x : J8Physical.Wire (Subdivision Pair Row)), ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
    (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
    (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) := by
  classical
  dsimp only
  let d := physicalLayout row col two z seat preserves
  let e := endpointLayout row col two z seat preserves hR hC hP
  have even : Even (2^(t+1) : ℕ) := ⟨2^t, by rw [pow_succ]; omega⟩
  exact ⟨fun p x => J8Physical.shift_reads_no_pins d e p x,
    fun _ _ h => J8Physical.shift_stays_in_child d even h,
    fun p => J8Physical.pin_targets_nonempty d p (pin_head_off row col two z hz seat preserves p)⟩

#print axioms pin_wire_identifies
#print axioms pin_head_off
#print axioms compiled_probe

end
end J7ToJ8Certificate
