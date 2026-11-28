import J8RelaxedWiring
import J9R20SameFileGeometry

namespace Paper6JointSeating
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout
open J7FullWordAssembly J7ToJ8Certificate J7ToJ8Canonical J7SeatPacking J7SeatRounded J7PrintedParamsGraph
open J6R10Repack J6R9PacketScopes J8Physical J6R14SpecializedBox J1PPrinted J9R20SameFile

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

variable {A Pair Row Col W : Type} [LinearOrder A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W → Row) (col : W → OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2) (z : DState A Pair Row Col t)
variable (seat : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
local notation "d" => physicalLayout row col two z seat preserve

theorem relaxed_endpoint_of_raw
    (nonp : ∀ w s, (seat w).2 = endpointIndex (t+1) s → nonpin col w)
    (first : Set.InjOn (rowNode row) {w | (seat w).2 = endpointIndex (t+1) false}) :
    J8Physical.Relaxed.RowEndpointSeating d := by
  constructor
  · intro x y hx hy hxy
    let j := rowWire (Pair:=Pair) row two
    change (seat (j x)).2.val = 0 at hx
    change (seat (j y)).2.val = 0 at hy
    have hx' : (seat (j x)).2 = endpointIndex (t+1) false := Fin.ext hx
    have hy' : (seat (j y)).2 = endpointIndex (t+1) false := Fin.ext hy
    apply j.injective
    exact first hx' hy' ((rowWire_owner row two x).trans (hxy.trans (rowWire_owner row two y).symm))
  · intro y hy
    let j := rowWire (Pair:=Pair) row two
    change (seat (j y)).2.val = 2^(t+1)-1 at hy
    have hy' : (seat (j y)).2 = endpointIndex (t+1) true := Fin.ext hy
    obtain ⟨v,hv⟩ := nonp (j y) true hy'
    have hown := (owner_layout row col two z seat preserve y).trans hv
    cases yy : (d).column y with
    | inl p => simp [J8Physical.colOwner,yy] at hown
    | inr q => exact ⟨q,rfl⟩

theorem off_of_raw_label
    (cross : ∀ p : Pin Pair, ((wordLabel row col z (pinEmbed Pair W p)) 0).1 ≠
      ((wordLabel row col z (pinEmbed Pair W p)) 0).2) :
    ∀ p : Pin Pair, (d).rowLabel (pinWire d p).1 ≠ (d).pinLabel p := by
  intro p
  have eq := J7R13.actual_cell row col z (pinEmbed Pair W p)
  have rwP := pin_wire_identifies row col two z seat preserve p
  have h := cross p
  rw [eq] at h
  change J7R13.rowFull z (rowNode row (pinEmbed Pair W p)) 0 ≠
    J7R13.colFull z (colNode col (pinEmbed Pair W p)) 0 at h
  rw [← rwP,rowWire_owner] at h
  exact h

#print axioms relaxed_endpoint_of_raw
#print axioms off_of_raw_label
end
end Paper6JointSeating


