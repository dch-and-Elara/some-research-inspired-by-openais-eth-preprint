import J6R16ModeCostBranchFold
import J6R24MeteredRecursionLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 50000000
set_option maxRecDepth 8000

/-! Native occurrence recurrence: every actual Plan slot has its own
term, including repeated Call records and disjoint scoped visits.
The local charge premises are intentionally visible; this is not a
proof of an installed runner's missing per-frame cost receipt. -/
namespace J6R49Cost
open scoped BigOperators Classical Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J6R11Blueprint
open J6R16ModeCost J6R24MeteredRecursion

private theorem sum_le_add_sum {X : Type*} (xs : List X) (u v w : X → ℕ)
    (h : ∀ x∈xs,u x ≤ v x+w x) :
    (xs.map u).sum ≤ (xs.map v).sum+(xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hh := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons]
    omega

theorem level_charge_le {X : Type*} (P : FinitePlan X) (r : X)
    (total localFee : X → ℕ) (d : ℕ)
    (h : ∀ x∈occurrences P r d,total x ≤ localFee x+((childList P x).map total).sum) :
    levelBill P r total d ≤ levelBill P r localFee d+levelBill P r total (d+1) := by
  rw [next_level_bill,levelBill,levelBill]
  exact sum_le_add_sum _ _ _ _ h

theorem scoped_occurrence_ledger_le {X : Type*} (P : FinitePlan X) (r : X)
    (total localFee : X → ℕ) (H : ℕ)
    (h : ∀ d x,x∈occurrences P r d → 
        total x ≤ localFee x+((childList P x).map total).sum)
    (terminal : occurrences P r (H+1)=[]) :
    total r ≤ ∑ j∈Finset.range (H+1),levelBill P r localFee j := by
  have chain (n : ℕ) :
      levelBill P r total 0 ≤ (∑ j∈Finset.range n,levelBill P r localFee j)+levelBill P r total n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h' := level_charge_le P r total localFee n (h n)
      rw [Finset.sum_range_succ]
      omega
  simpa only [levelBill,show occurrences P r 0=[r] from rfl,terminal,List.map_nil,
    List.map_cons,List.sum_cons,List.sum_nil,Nat.add_zero] using chain (H+1)

theorem local_charge_affine_le {own n fixed address b e : ℕ}
    (h : own ≤ fixed+address*n) (hn : n ≤ 2^(b+e)) :
    own ≤ (fixed+address)*2^(b+e) := by
  have hp : 0<(2:ℕ)^(b+e) := Nat.pow_pos (by decide)
  rw [Nat.add_mul]
  exact h.trans (Nat.add_le_add (Nat.le_mul_of_pos_right _ hp) (Nat.mul_le_mul_left _ hn))

theorem affine_occurrence_tree_bound {X : Type*} (P : FinitePlan X) (r : X)
    (s C lam K b H fixed address : ℕ) (total localFee : X → ℕ)
    (terminal : occurrences P r (H+1)=[])
    (hSlots : ∀ j c,c∈occurrences P r j →
      Nat.card (P.Slot c) ≤ 2^(b+depthExponent s C lam K j))
    (runStep : ∀ j c,c∈occurrences P r j →
      total c ≤ localFee c+((childList P c).map total).sum)
    (ownBound : ∀ j c,c∈occurrences P r j →
      localFee c ≤ fixed+address*Nat.card (P.Slot c)) :
    total r ≤ (H+1)*(fixed+address)*2^(b*(H+1)+24*depthScale s C lam K) :=
  (scoped_occurrence_ledger_le P r total localFee H runStep terminal).trans
    (total_fee_bound P r s C lam K b (H+1) (fixed+address) localFee hSlots
      (fun j c hc => local_charge_affine_le (ownBound j c hc) (hSlots j c hc)))

#print axioms level_charge_le
#print axioms scoped_occurrence_ledger_le
#print axioms local_charge_affine_le
#print axioms affine_occurrence_tree_bound
end J6R49Cost

