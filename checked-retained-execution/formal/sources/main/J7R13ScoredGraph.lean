import J7R13Native
import J7R13Physical

/-! One selected full labeling and one chart simultaneously support both native interfaces. -/
open scoped Classical BigOperators
namespace J7R13
open J7LiteralGraph J7PrintedParams J7PrintedParamsGraph J7SourceLabels J7FullWordCells
open J7SeatSource J7SeatPacking J7SeatRounded J7ToJ8Incidence J7ToJ8Layout J7ToJ8Canonical
open P11FullPacking J6R10Repack
noncomputable section
set_option maxHeartbeats 2500000

variable {V A : Type*} [LinearOrder V] [Fintype V] [LinearOrder A] [AddCommGroup A] [Fintype A]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (cubic : Cubic H)

theorem scored_physical_of_cubic (hA : Fintype.card A = 64)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin (Edge H)))) :
    let N := Fintype.card (Pin (Edge H))
    let t := rootT (sourceSize N)
    let col := column (atlas H cubic) cycle
    let row : OrdinaryWire (Edge H) (TEdge H) → OrdinaryRow (Edge H) (TEdge H) := Prod.fst
    let E := Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H))
    leafThreshold (sourceSize N) < 24*N ∧
    ∃ z : DState A (Edge H) (OrdinaryRow (Edge H) (TEdge H)) (OldNonPrivate (Edge H) (TEdge H)) t,
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
      ∃ j : E ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel row col z w,
      ∃ budget : Nat.card (Page (t+1) b' A)*2^(t+1) ≤ 3*Nat.card E,
      let d := physicalLayout row col ordinary_row_exact_two z j preserve
      let P := asPacking row col z j preserve budget
      JointScore row col z ≤ 32*(Nat.card E:ℚ) ∧
      varianceScore (declaredCell (network row col) P.rowLabel P.colLabel) ≤
        2*(Nat.card E:ℚ)*rootDelta (sourceSize N) ∧
      P.copies = ceilCopies (2^(t+1)) (maxFiber (declaredCell (network row col) P.rowLabel P.colLabel)) ∧
      (∀ w, d.seat w = P.seat (rowWire row ordinary_row_exact_two w)) ∧
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      Nonempty (J8Physical.EndpointSeating d) ∧
      (∀ p x, ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
      (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
      (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) := by
  dsimp only
  obtain ⟨hactive,z,hp,hscore,hvar,j,hseat,hfill,hend,hnopin,htarget,heach⟩ :=
    scored_native_of_cubic H cubic hA large
  let E := Wire (Edge H) (OrdinaryWire (Edge H) (TEdge H))
  have hE : Nat.card E = 24*Fintype.card (Pin (Edge H)) :=
    (Nat.card_eq_fintype_card (α:=E)).trans (actual_incidence (atlas H cubic)).1
  have hb := hp.trans_eq (congrArg (fun n : ℕ => 3*n) hE.symm)
  refine ⟨hactive,z,j,hseat,hb,?_,hvar,?_,?_,hfill,hend,hnopin,htarget,heach⟩
  · simpa only [Nat.card_eq_fintype_card] using hscore
  · exact asPacking_minimal _ _ z j hseat hb rfl
  · intro w
    exact same_J8_seat _ _ z j hseat hb ordinary_row_exact_two w

#print axioms scored_physical_of_cubic
end
end J7R13
