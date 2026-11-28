import J7ToJ8Certificate
import J7R13Collision
import J7R13Seat

/-! # Full finite J7 selection and exact rounding feed the J8 probe -/
open scoped BigOperators Classical

namespace J7R13

open J7SourceLabels J7FullWordCells J7FullWordAssembly J7SeatSource
open J7SeatPacking J7SeatCertificate J7SeatMatching J7SeatRounded P11FullPacking
open J7ToJ8Incidence J7ToJ8Layout J7ToJ8Certificate

noncomputable section
set_option maxHeartbeats 3500000

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}

/-- Start with a physical graph, exact ordinary subdivision incidence
and the finite J7 slack bounds. Choose the full source words and matching,
use the source's actual maximum-load padding, and feed the resulting
literal packet placement directly to the J8 physical layout. -/
theorem compile_selected_scored
    (h : 2 ≤ Fintype.card A)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_two : ∀ r, Nat.card {w : W // row w = r} = 2)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A (Fin t → A) Pair Row Col) (ref : Seed A (Fin t → A))
    (B : ℕ) (ρ δ : ℚ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (devWord : 32*(Fintype.card (Wire Pair W) : ℚ) ≤ ρ^2)
    (cap : allCenter A Pair W t + ρ ≤ b*(2:ℚ)^(t+1))
    (degree : ∀ (w : {w // nonpin col w}),
      (nearby (fun p => rowNode row p.val) (fun p => colNode col p.val) w).card ≤ B)
    (devMark : (Nat.card {w // nonpin col w} : ℚ)*(B:ℚ)^2 ≤ δ^2)
    (endMargin : (2*b:ℚ)+δ ≤ (allCenter A Pair W t - pinCap A Pair t - 2*ρ)*(1/2:ℚ)^B) :
    ∃ z : State A (Fin t → A) Pair Row Col,
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
      b' ≤ b ∧ JointScore row col z ≤ 32*(Fintype.card (Wire Pair W):ℚ) ∧ ∃ j : Wire Pair W ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel row col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let d := physicalLayout row col row_two z j preserve
      Nonempty (J8Physical.EndpointSeating d) ∧
      (∀ p (x : J8Physical.Wire (Subdivision Pair Row)), ¬ J8Physical.Shift d x (J8Physical.pinWire d p)) ∧
      (∀ x y, J8Physical.Shift d x y → d.rowLabel x.1 = J8Physical.actualColLabel d y) ∧
      (∀ p, (J8Physical.targets d (J8Physical.pinWire d p)).Nonempty) := by
  classical
  obtain ⟨z,hscore,j,hz,hword,hfill,hR,hC,hP⟩ :=
    selected_and_seated_scored h row col row_cap clone_cap col_cap reference ref B ρ δ hρ hδ devWord cap degree devMark endMargin
  -- The first construction already seats every real wire without moving
  -- its cell; counting the target fibre gives the needed capacity for z.
  have capacity (c : Cell (Fin (t+1)) A) :
      Nat.card {w // wordLabel row col z w = c} ≤ b*2^(t+1) := by
    let e : {w // wordLabel row col z w = c} ↪ SlotFiber (b:=b) c :=
      ⟨fun w => ⟨j w.val,(hword w.val).trans w.prop⟩,
        fun _ _ he => Subtype.ext (j.injective (congrArg Subtype.val he))⟩
    exact (Nat.card_le_card_of_injective e e.injective).trans_eq (card_slots (b:=b) c)
  obtain ⟨hb,k,hpres,hfull,hR',hC',hP'⟩ :=
    seat_at_rounded_max row col z hz capacity j hword hfill hR hC (fun p => (hP p).1)
  exact ⟨z,hb,hscore,k,hpres,hfull,⟨endpointLayout row col row_two z k hpres hR' hC' (fun p => (hP' p).1)⟩,
    compiled_probe row col row_two z hz k hpres hR' hC' (fun p => (hP' p).1)⟩

#print axioms compile_selected_scored

end
end J7R13
