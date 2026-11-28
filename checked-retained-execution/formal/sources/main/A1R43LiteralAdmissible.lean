import A1R43LiteralGeneralEstimate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

/-! The printed pairing lemma applies to any simulated degree bound that
fits the actual planned source degree, not only degree three or six.
This proves geometry, independent of a supplied original entry evaluator. -/
namespace A1R43Literal.General
open scoped Classical
open J6R10Repack P11FullPacking J1PPrinted
noncomputable section

variable {U A B : Type} [Fintype U] [Fintype A] [Fintype B]
variable (T : Network U A B)
local notation "m" => Nat.card U
local notation "a" => smallA m
local notation "b" => copies m

theorem printed_arbitrary_admissible_pair_plan (k : ℕ)
    (guard : PrintedMargins m) (hk : k≤sourceDelta (starSize m))
    (hA : ∀ r,Nat.card {u : U//T.row u=r}≤k)
    (hB : ∀ c,Nat.card {u : U//T.col u=c}≤k) :
    ∃ W : PairPlan T a b,
      Nat.card (SplitWire U (Spare T W)) = floorWires m ∧
      J9PrintedSchedule.leafThreshold (starSize m) (Nat.clog 2 (starSize m)) <
        Nat.card (SplitWire U (Spare T W)) ∧
      Nat.card (SplitWire U (Spare T W))≤starSize m ∧
      (∀ c, Nat.card (Fiber (declaredCell (splitNetwork T (Spare T W))
        (fullPacking T W).rowLabel (fullPacking T W).colLabel) c) = b*lengthL m) ∧
      varianceScore (declaredCell (splitNetwork T (Spare T W))
        (fullPacking T W).rowLabel (fullPacking T W).colLabel)=0 ∧
      ∀ u, ((fullPacking T W).seat (oddWire U (Spare T W) u)).1 =
          ((fullPacking T W).seat (evenWire U (Spare T W) u)).1 ∧
        ((fullPacking T W).seat (evenWire U (Spare T W) u)).2.val+1 =
          ((fullPacking T W).seat (oddWire U (Spare T W) u)).2.val := by
  obtain ⟨r,c,_h,cap⟩ := chosen_simulation_capacity T a (b*2^a) k hA hB
    (collision_for_real_degree _ k guard hk) guard.paired_capacity
  let W : PairPlan T a b := ⟨0,r,c,cap⟩
  have hfull : Nat.card (SplitWire U (Spare T W)) = floorWires m := by
    rw [full_wire_count T W,guard.full_dim,lower_word_cell_count]
    rfl
  refine ⟨W,hfull,?_,?_,?_,full_collision_zero T W,full_seat_predecessor T W⟩
  · rw [hfull]
    exact guard.active_half.trans_le guard.wire_window.1
  · rw [hfull]
    exact guard.wire_window.2
  · intro c
    rw [full_cell_load T W c,guard.full_dim]
    rfl

#print axioms printed_arbitrary_admissible_pair_plan
end
end A1R43Literal.General
