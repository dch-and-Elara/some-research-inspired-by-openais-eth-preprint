import J7LiteralGraphNative
import J7R13Literal

/-! # Actual simple edges and the native literal four-clone graph interface -/
open scoped BigOperators Classical

namespace J7R13
open J7LiteralGraph
open J7SourceLabels J7PrintedParams J7PrintedParamsGraph
open J7FullWordCells J7SeatSource J7SeatPacking J7SeatRounded P11FullPacking
open J7ToJ8Incidence J7ToJ8Layout J7ToJ8Canonical

noncomputable section
set_option maxHeartbeats 1500000

variable {V : Type*} [LinearOrder V] (H : SimpleGraph V) [Fintype V] [DecidableRel H.Adj]
variable (cubic : Cubic H)

variable {A : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]

/-- The J7/J8 printed root for genuine ordered triangle replacement.
No incidence atlas is supplied: it is computed by sorting the actual
base graph's local neighbors and choosing the fixed triangle cycle. -/
theorem scored_native_of_cubic (hA : Fintype.card A = 64)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin (Edge H)))) :
    let N := Fintype.card (Pin (Edge H))
    let t := rootT (sourceSize N)
    let col := column (atlas H cubic) cycle
    leafThreshold (sourceSize N) < 24*N ∧
    ∃ z : State A (Fin t → A) (Edge H) (OrdinaryRow (Edge H) (TEdge H)) (OldNonPrivate (Edge H) (TEdge H)),
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel Prod.fst col z))
      Nat.card (Page (t+1) b' A)*printedL t ≤ 3*(24*N) ∧
      JointScore Prod.fst col z ≤ 32*(Fintype.card (Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H))):ℚ) ∧
      J6R10Repack.varianceScore (J6R10Repack.declaredCell (network Prod.fst col) (rowFull z) (colFull z)) ≤
        2*(Nat.card (Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H))):ℚ)*rootDelta (sourceSize N) ∧
      ∃ j : Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H)) ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel Prod.fst col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let d := physicalLayout Prod.fst col ordinary_row_exact_two z j preserve
      Nonempty (J8Physical.EndpointSeating d) ∧
      (∀ p (x : J8Physical.Wire (Subdivision (Edge H) (OrdinaryRow (Edge H) (TEdge H)))),
        ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
      (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
      (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) :=
  literal_four_clone_scored_root hA (atlas H cubic) large

#print axioms scored_native_of_cubic

end
end J7R13
