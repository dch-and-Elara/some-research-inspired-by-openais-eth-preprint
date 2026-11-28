import J6R14SpecializedBoxPreservedMode
import J6R15SpecializedBoxFileTruth

/-! Pull the actual J7 packing back to the physical J8 wire type. This
changes names only: endpoint incidence, all word coordinates, exact
packet positions, and the padded resource bound are carried over. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R10Repack
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J7SeatPacking
noncomputable section
set_option linter.unusedSectionVars false

section Pull
variable {A B E E' G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} {N' : Network E' A B}
variable (e : E ≃ E') (hr : ∀ w, N'.row (e w)=N.row w)
variable (hc : ∀ w, N'.col (e w)=N.col w)
variable (Q : PhysicalPacking N' a G)

def pullPacking : PhysicalPacking N a G where
  rowLabel := Q.rowLabel
  colLabel := Q.colLabel
  copies := Q.copies
  mask := Q.mask
  seat := e.toEmbedding.trans Q.seat
  exactCell w := by
    change physicalCell Q.mask (Q.seat (e w)) = declaredCell N Q.rowLabel Q.colLabel w
    rw [Q.exactCell]
    unfold declaredCell
    simp only [hr,hc]
  paddedBudget := by rw [Nat.card_congr e]; exact Q.paddedBudget

theorem pullPacking_same_address (w : E) :
    (pullPacking e hr hc Q).seat w = Q.seat (e w) := rfl

end Pull

variable {A Pair Row Col W : Type} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W→Row) (col : W→OrdinaryColumn Pair Col)
variable (two : ∀ w, Nat.card {e : W // row e=w}=2)
variable (z : DState A Pair Row Col t)
variable (j : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w)
variable (budget : Nat.card (Page (t+1) b A)*2^(t+1) ≤ 3*Nat.card (Wire Pair W))

local notation "d₀" => physicalLayout row col two z j preserve
local notation "Q₀" => J7R13.asPacking row col z j preserve budget
local notation "i₀" => (Fin.mk 0 (Nat.succ_pos t))

def asOrientedSeat : PhysicalPacking (orientedNetwork d₀) (t+1) A :=
  pullPacking (rowWire row two) (rowWire_owner row two)
    (fun w => (owner_layout row col two z j preserve w).symm) Q₀

theorem asOrientedSeat_literal_address (w : J8Physical.Wire (Subdivision Pair Row)) :
    (asOrientedSeat row col two z j preserve budget).seat w = (d₀).seat w := rfl

theorem asOrientedSeat_row (w : J8Physical.Wire (Subdivision Pair Row)) :
    rowGroup (asOrientedSeat row col two z j preserve budget).mask i₀ ((d₀).seat w) =
      (d₀).rowLabel w.1 :=
  preserved_row_chart row col two z j preserve budget w

theorem asOrientedSeat_col (w : J8Physical.Wire (Subdivision Pair Row)) :
    colGroup (asOrientedSeat row col two z j preserve budget).mask i₀ ((d₀).seat w) =
      J8Physical.actualColLabel d₀ w :=
  preserved_col_chart row col two z j preserve budget w

#print axioms pullPacking
#print axioms pullPacking_same_address
#print axioms asOrientedSeat
#print axioms asOrientedSeat_literal_address
#print axioms asOrientedSeat_row
#print axioms asOrientedSeat_col
end
end J6R14SpecializedBox