import J7R43LiteralCloneGeometry
import J7R43LiteralEvaluator

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

variable (e : EndpointSeating (physicalLayout row col two z j preserve)) (even : Even (2^(a+1):ℕ))
variable (p ell created : ℕ) (f : ℤ[X]) (hf : f.Monic) (hc0 : 0<created)
variable (hf0 : 0<f.natDegree) (hell : 0<ell)
variable (F : OldTables (physicalLayout row col two z j preserve)) (sign : Pin Pair→Bool)
local notation "file" => (orientedEntryFile d₀ f ell created F sign)

set_option maxHeartbeats 4200000 in
include hc0 hf0 hell in
theorem same_four_clone_baseline
    (ht : (L₀:ℤ)-1≠0) (hv : padicValInt 2 ((L₀:ℤ)-1)=(i₀).val) (g : A) :
    reduce p f ell (actualChildTruth Q₀ i₀ ht hv p 0 file hf 0 g) =
      (integerBaseline d₀ e even F g : Box f ell p) := by
  exact physical_baseline_no_division d₀ (Q₀).mask (Q₀).rowLabel (Q₀).colLabel (Q₀).exactCell
    (Q₀).paddedBudget i₀ hr₀ hc₀ (literal_row_heads row col two z j preserve budget)
    (literal_pin_heads row col two z j preserve budget) (literal_old_heads row col two z j preserve budget)
    p created F sign hf hc0 hf0 hell e even (by positivity) ht hv g

set_option maxHeartbeats 5000000 in
include hc0 hf0 hell in
theorem same_four_clone_singleton
    (ht : (L₀:ℤ)-1≠0) (hv : padicValInt 2 ((L₀:ℤ)-1)=(i₀).val)
    (s : Pin Pair) (off : (d₀).rowLabel (pinWire d₀ s).1≠(d₀).pinLabel s)
    (n : Fin (@Fintype.card (PinTile d₀ s) (canonicalPinTile d₀ s))) (hn : n.val<p-1)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F ((d₀).pinLabel s) v) x=true) :
    let m := anchoredMode d₀ (Q₀).mask i₀ hr₀ hc₀ s off (⟨n.val,hn⟩ : Fin (p-1))
    reduce p f ell (actualChildTruth Q₀ i₀ ht hv p 0 file hf (Finsupp.single m 1) ((d₀).pinLabel s)) =
      (integerSourceEvaluation d₀ e even F sign s n.val : Box f ell p) := by
  exact physical_source_no_division d₀ (Q₀).mask (Q₀).rowLabel (Q₀).colLabel (Q₀).exactCell
    (Q₀).paddedBudget i₀ hr₀ hc₀ (literal_row_heads row col two z j preserve budget)
    (literal_pin_heads row col two z j preserve budget) (literal_old_heads row col two z j preserve budget)
    p created F sign hf hc0 hf0 hell e even (by positivity) rfl ht hv s off n hn sat

#print axioms same_four_clone_baseline
#print axioms same_four_clone_singleton
end
end J7R43Literal