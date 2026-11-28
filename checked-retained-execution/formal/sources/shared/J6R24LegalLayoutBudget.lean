
import J6R24LegalLayoutTable
import J6R14LayoutCostPoly

/-! Substitute the actual printed compact dimensions into the ordered
seat compiler. Its complete address table is exactly M, and the cost
of generating the dense key menu is not a free factor. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6OrientedHost J6R14LayoutCost AOracleMachineTime
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false

def printedRankWidth (m : ℕ) : ℕ := a m+Nat.clog 2 (K m)+1

def printedHalf (m : ℕ) : ℕ := L m/2

theorem printed_half_correct (m : ℕ) : 2*printedHalf m=L m := by
  obtain ⟨d,h⟩ := (mesh_seats m).2.2
  unfold printedHalf
  omega

theorem printed_room (m : ℕ) : m≤K m := by
  have h := (mesh_seats m).2.1
  omega

theorem printed_rank_width (m : ℕ) :
    0<printedRankWidth m ∧ a m≤printedRankWidth m ∧ K m*L m<2^printedRankWidth m := by
  refine ⟨by unfold printedRankWidth; omega,by unfold printedRankWidth; omega,?_⟩
  have P : K m≤2^Nat.clog 2 (K m) := Nat.le_pow_clog (by decide) _
  calc
    K m*L m≤2^Nat.clog 2 (K m)*L m := Nat.mul_le_mul_right _ P
    _ = 2^(a m+Nat.clog 2 (K m)) := by rw [J6Mesh.L,mul_comm,←pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by unfold printedRankWidth; omega)

theorem printed_menu_identity (m : ℕ) : 2^(6*a m)*2^(6*a m)=D m := by
  rw [source_menu_size _ _ rfl]
  exact cell_palette m

theorem complete_rank_tape_length (a b : ℕ) :
    (fullRankOrder a b).length=(2^(6*a)*2^(6*a))*(b*2^a) := by
  have h := congrArg List.length (typed_cells_exact a).2.2
  rw [List.length_map,allPairs_len] at h
  unfold fullRankOrder
  exact (List.length_product (typedCells a) (List.finRange (b*2^a))).trans (by rw [List.length_finRange,h])

def printedSeatBudget (m : ℕ) :=
  menuPoly (6*a m) (M m)+M m*(stepFee (a m) (printedRankWidth m)+
    appendFee (a m) (printedRankWidth m)+10)+11

theorem physical_complete_seat_budget (m : ℕ) :
    completeSeatFee (a m) (K m) (printedRankWidth m)≤printedSeatBudget m := by
  have hd : D m≤M m := by
    rw [←mesh_product]
    have hp : 0<K m*L m := by unfold J6Mesh.K J6Mesh.L; positivity
    exact Nat.le_mul_of_pos_right _ hp
  have hc := allPairsCap_poly (6*a m) (M m) ((printed_menu_identity m).trans_le hd)
  unfold completeSeatFee cellSeatFee printedSeatBudget
  rw [printed_menu_identity m]
  change allPairsCap (6*a m)+5+D m*(4+(K m*L m)*stepFee _ _+
    (K m*L m)*appendFee _ _+6)+6≤_
  have E : D m*(4+(K m*L m)*stepFee (a m) (printedRankWidth m)+
      (K m*L m)*appendFee (a m) (printedRankWidth m)+6)=
      (D m*(K m*L m))*(stepFee (a m) (printedRankWidth m)+appendFee (a m) (printedRankWidth m))+10*D m := by ring
  rw [E,mesh_product,Nat.mul_add _ _ 10]
  omega

theorem printed_seats_paid (m : ℕ) :
    let out := allSeatWords (a m) (K m) (printedRankWidth m)
    out.result.length=M m ∧ out.steps≤printedSeatBudget m := by
  obtain ⟨h0,h1,h2⟩ := printed_rank_width m
  obtain ⟨h,c⟩ := complete_tape_exact (a m) (K m) (printedRankWidth m) h0 h1 h2
  refine ⟨?_,c.trans (physical_complete_seat_budget m)⟩
  rw [h,List.length_map,complete_rank_tape_length,printed_menu_identity m]
  exact mesh_product m

#print axioms printed_half_correct
#print axioms printed_room
#print axioms printed_rank_width
#print axioms printed_menu_identity
#print axioms complete_rank_tape_length
#print axioms physical_complete_seat_budget
#print axioms printed_seats_paid
end J6R24LegalLayout
