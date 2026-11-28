import J7R13Collision
import J7SeatRounded

/-! Use the preserved J8 seat itself as the source repacker's physical seat. -/
open scoped Classical BigOperators
namespace J7R13
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J7SeatPacking J7SeatRounded
open P11FullPacking J6R10Repack
noncomputable section

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W → Row) (col : W → OrdinaryColumn Pair Col)
variable (z : DState A Pair Row Col t)
variable (j : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w)
variable (budget : Nat.card (Page (t+1) b A)*2^(t+1) ≤ 3*Nat.card (Wire Pair W))

/-- Same actual vertices, labels, fold mask, and occupied addresses. There is
no invocation of rounded repacking which could independently change the seat. -/
def asPacking : PhysicalPacking (network row col) (t+1) A where
  rowLabel := rowFull z
  colLabel := colFull z
  copies := b
  mask := balancedMask _ _
  seat := j
  exactCell w := (preserve w).trans (actual_cell row col z w)
  paddedBudget := by
    rw [← total_slots (balancedMask (K:=A) (t+1) b)]
    exact budget

omit [AddCommGroup A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem same_J8_seat (two : ∀ r, Nat.card {w : W // row w = r} = 2)
    (x : J8Physical.Wire (Subdivision Pair Row)) :
    (physicalLayout row col two z j preserve).seat x =
      (asPacking row col z j preserve budget).seat (rowWire row two x) := rfl

omit [AddCommGroup A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
/-- On the same J8 wire, the two literal port owners and retained coordinate
agree with the full finite-ring source network. -/
theorem same_J8_owner_word (two : ∀ r, Nat.card {w : W // row w = r} = 2)
    (x : J8Physical.Wire (Subdivision Pair Row)) :
    let n := network row col
    let d := physicalLayout row col two z j preserve
    let P := asPacking row col z j preserve budget
    let e : Wire Pair W := rowWire row two x
    n.row e = x.1 ∧ n.col e = J8Physical.colOwner d x ∧
      P.rowLabel (n.row e) 0 = d.rowLabel x.1 ∧
      P.colLabel (n.col e) 0 = J8Physical.actualColLabel d x := by
  dsimp only
  refine ⟨rowWire_owner row two x,(owner_layout row col two z j preserve x).symm,?_,?_⟩
  · change rowFull z (rowNode row (rowWire row two x)) 0 = subdivisionHead z x.1
    rw [rowWire_owner,rowFull_head]
  · change colFull z (colNode col (rowWire row two x)) 0 =
      J8Physical.actualColLabel (physicalLayout row col two z j preserve) x
    rw [colFull_head,← owner_layout row col two z j preserve x]
    unfold J8Physical.actualColLabel J8Physical.colOwner
    cases (physicalLayout row col two z j preserve).column x <;> rfl

omit [AddCommGroup A] [Fintype Row] [Fintype Col] in
theorem asPacking_minimal
    (hb : b = ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))) :
    let P := asPacking row col z j preserve budget
    P.copies = ceilCopies (2^(t+1)) (maxFiber (declaredCell (network row col) P.rowLabel P.colLabel)) := by
  change b = ceilCopies _ (maxFiber (declaredCell (network row col) (rowFull z) (colFull z)))
  rw [← funext (actual_cell row col z)]
  exact hb

#print axioms asPacking
#print axioms same_J8_seat
#print axioms same_J8_owner_word
#print axioms asPacking_minimal

end
end J7R13
