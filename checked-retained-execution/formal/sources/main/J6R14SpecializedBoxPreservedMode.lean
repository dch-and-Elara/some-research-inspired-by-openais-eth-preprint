import J6R14SpecializedBoxPackedFile
import J6R14SpecializedBoxModeChart

/-! Specialize the address bridge to the *preserved* R13 source
packing. No separate row/column chart equalities are now required
from a caller; they come from exactCell on the actual occupied wire
and the original source incidence owner theorems. -/
namespace J6R14SpecializedBox
open scoped Classical
open P11FullPacking J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout
open J6R9PacketScopes J7SeatPacking

noncomputable section
variable {A Pair Row Col W : Type} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b p : ℕ}
variable (row : W→Row) (col : W→OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2)
variable (z : DState A Pair Row Col t)
variable (j : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w)
variable (budget : Nat.card (Page (t+1) b A)*2^(t+1) ≤ 3*Nat.card (Wire Pair W))

local notation "d₀" => physicalLayout row col two z j preserve
local notation "Q₀" => J7R13.asPacking row col z j preserve budget
local notation "i₀" => ((0:Fin (t+1)))
local notation "e₀" => rowWire (Pair:=Pair) row two

set_option linter.unusedSectionVars false in
theorem preserved_row_chart (x : J8Physical.Wire (Subdivision Pair Row)) :
    rowGroup (Q₀).mask i₀ ((d₀).seat x) = (d₀).rowLabel x.1 := by
  have h := congrArg Prod.fst (congrFun ((Q₀).exactCell (e₀ x)) i₀)
  exact h.trans (J7R13.same_J8_owner_word row col z j preserve budget two x).2.2.1

set_option linter.unusedSectionVars false in
theorem preserved_col_chart (x : J8Physical.Wire (Subdivision Pair Row)) :
    colGroup (Q₀).mask i₀ ((d₀).seat x) = J8Physical.actualColLabel d₀ x := by
  have h := congrArg Prod.snd (congrFun ((Q₀).exactCell (e₀ x)) i₀)
  exact h.trans (J7R13.same_J8_owner_word row col z j preserve budget two x).2.2.2

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1800000 in
theorem actual_preserved_singleton (a : Pin Pair) (n : Fin (p-1))
    (off : (d₀).rowLabel (J8Physical.pinWire d₀ a).1 ≠ (d₀).pinLabel a) :
    ∃ m : Mode i₀ p (Q₀).mask,
      m.order=n ∧ source (Q₀).mask i₀ m = (d₀).pinLabel a ∧
      target (Q₀).mask i₀ m = (((d₀).seat (J8Physical.pinWire d₀ a)).1,(d₀).rowLabel (J8Physical.pinWire d₀ a).1) ∧
      (∀ x, rowBlock (Q₀).mask i₀ ((d₀).seat x) = target (Q₀).mask i₀ m ↔
        x ∈ J8Physical.targets d₀ (J8Physical.pinWire d₀ a)) ∧
      Finsupp.single m 1 ∈ J6RecursiveMenu.menu p (J6R10RowAffine.weight i₀ p (Q₀).mask) := by
  let hr := preserved_row_chart row col two z j preserve budget
  let hc := preserved_col_chart row col two z j preserve budget
  refine ⟨anchoredMode d₀ (Q₀).mask i₀ hr hc a off n,rfl,?_⟩
  exact ⟨anchored_source d₀ (Q₀).mask i₀ hr hc a off n,
    anchored_target d₀ (Q₀).mask i₀ hr hc a off n,
    anchored_actual_target_iff d₀ (Q₀).mask i₀ hr hc rfl a off n,
    anchored_singleton_legal d₀ (Q₀).mask i₀ hr hc a off n⟩

#print axioms preserved_row_chart
#print axioms preserved_col_chart
#print axioms actual_preserved_singleton
end
end J6R14SpecializedBox
