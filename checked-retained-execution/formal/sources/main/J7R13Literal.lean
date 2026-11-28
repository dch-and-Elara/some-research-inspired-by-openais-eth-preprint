import J7R13Root
import J7PrintedParamsGraph

/-! # Native root generated from actual four-clone literal incidence atlas -/
open scoped BigOperators Classical

namespace J7R13
open J7PrintedParams
open J7PrintedParamsGraph J7SourceLabels J7FullWordCells J7SeatSource
open J7SeatPacking J7SeatRounded P11FullPacking J7ToJ8Incidence J7ToJ8Layout
open J7ToJ8Canonical

noncomputable section

variable {A Pair G : Type*} [LinearOrder A] [AddCommGroup A]
variable [Fintype A] [Fintype Pair] [Fintype G]

/-- Once a cubic graph's actual incidences have been numbered in three
slots at each vertex and the exterior matching pairs index its pins, no
remaining physical counts, row degree, column degree, reference labels,
packing inequalities, or arithmetic margins need be supplied. -/
theorem literal_four_clone_scored_root
    (hA : Fintype.card A = 64) (ends : G × Bool ≃ Pin Pair × Fin 3)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair))) :
    let N := Fintype.card (Pin Pair)
    let t := rootT (sourceSize N)
    let col := column ends cycle
    leafThreshold (sourceSize N) < 24*N ∧
    ∃ z : State A (Fin t → A) Pair (OrdinaryRow Pair G) (OldNonPrivate Pair G),
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel Prod.fst col z))
      Nat.card (Page (t+1) b' A)*printedL t ≤ 3*(24*N) ∧
      JointScore Prod.fst col z ≤ 32*(Fintype.card (Wire Pair (OrdinaryWire Pair G)):ℚ) ∧
      J6R10Repack.varianceScore (J6R10Repack.declaredCell (network Prod.fst col) (rowFull z) (colFull z)) ≤
        2*(Nat.card (Wire Pair (OrdinaryWire Pair G)):ℚ)*rootDelta (sourceSize N) ∧
      ∃ j : Wire Pair (OrdinaryWire Pair G) ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel Prod.fst col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let d := physicalLayout Prod.fst col ordinary_row_exact_two z j preserve
      Nonempty (J8Physical.EndpointSeating d) ∧
      (∀ p (x : J8Physical.Wire (Subdivision Pair (OrdinaryRow Pair G))),
        ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
      (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
      (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) := by
  classical
  dsimp only
  let N := Fintype.card (Pin Pair)
  let t := rootT (sourceSize N)
  let ref : Seed A (Fin t → A) := ((0,(0,0),(0,0)),fun _ _ => 0)
  have hi := actual_incidence ends
  refine four_clone_scored_root hA N hi.2 large rfl hi.1 Prod.fst (column ends cycle)
    ordinary_row_exact_two ?_ ?_ (fun _ => ref) ref
  · intro p
    convert clone_degree ends cycle p using 1
    congr 1
    exact Finset.ext fun w => by simp only [Finset.mem_filter]
  · intro c
    convert ordinary_degree ends cycle c using 1
    congr 1
    exact Finset.ext fun w => by simp only [Finset.mem_filter]

#print axioms literal_four_clone_scored_root

end
end J7R13
