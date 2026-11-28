import J6R16SpecializedBoxBinding

/-! Apply the one-group equalities to the preserved physical seating of
the original four-clone family. No row, column, or packet is moved. -/
namespace J7R43Literal
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J7SeatPacking
open J8Physical J8EndToEnd J8J9Grouped J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {A Pair Row Col W : Type} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {a b : ℕ}
variable (row : W→Row) (col : W→OrdinaryColumn Pair Col)
variable (two : ∀ v, Nat.card {w : W // row w=v}=2)
variable (z : DState A Pair Row Col a)
variable (j : J7SourceLabels.Wire Pair W ↪ Physical (a+1) b A)
variable (preserve : ∀ w, physicalCell (balancedMask (a+1) b) (j w) = wordLabel row col z w)
variable (budget : Nat.card (Page (a+1) b A)*2^(a+1) ≤ 3*Nat.card (J7SourceLabels.Wire Pair W))
local notation "d₀" => (physicalLayout row col two z j preserve)
local notation "Q₀" => (asOrientedSeat row col two z j preserve budget)
local notation "i₀" => (Fin.mk 0 (Nat.succ_pos a))
local notation "L₀" => (2^(a+1) : ℕ)
local notation "hr₀" => (asOrientedSeat_row row col two z j preserve budget)
local notation "hc₀" => (asOrientedSeat_col row col two z j preserve budget)

theorem seated_same_packing :
    seatedParentPacking d₀ (Q₀).mask (Q₀).rowLabel (Q₀).colLabel (Q₀).exactCell
      (Q₀).paddedBudget = Q₀ := by
  rfl

theorem literal_row_heads (r : Subdivision Pair Row) :
    (Q₀).rowLabel r i₀ = (d₀).rowLabel r := by
  change J7R13.rowFull z r i₀ = subdivisionHead z r
  have hz : i₀ = (0:Fin (a+1)) := Fin.ext rfl
  rw [hz]
  exact J7R13.rowFull_head z r

theorem literal_pin_heads (p : Pin Pair) :
    (Q₀).colLabel (.inl p) i₀ = (d₀).pinLabel p := by
  change J7R13.colFull z (.inl p) i₀ = pinHead z p
  have hz : i₀ = (0:Fin (a+1)) := Fin.ext rfl
  rw [hz]
  exact J7R13.colFull_head z (.inl p)

theorem literal_old_heads (v : OrdinaryColumn Pair Col) :
    (Q₀).colLabel (.inr v) i₀ = (d₀).colLabel v := by
  change J7R13.colFull z (.inr v) i₀ = columnHead z v
  have hz : i₀ = (0:Fin (a+1)) := Fin.ext rfl
  rw [hz]
  exact J7R13.colFull_head z (.inr v)
#print axioms seated_same_packing
#print axioms literal_row_heads
#print axioms literal_pin_heads
#print axioms literal_old_heads
end
end J7R43Literal