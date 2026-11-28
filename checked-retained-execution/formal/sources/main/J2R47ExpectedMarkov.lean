import J2R45BoundedErrorFree

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-! Markov clipping for the literal paid query tree with a nonempty finite
uniform seed set. No cap is placed on the zero path of the original tree. -/
namespace J2R47Expected
open scoped Classical BigOperators
open FiniteWeightedQueryTree J2R45BoundedError

universe u
variable {Q R W : Type*} {Seed : Type u}

theorem markov_cutoff (seeds : Finset Seed) (cost : Seed → ℕ) (T : ℕ)
    (mean : 12*(∑ i ∈ seeds,cost i) ≤ (T+1)*seeds.card) :
    12*(seeds.filter fun i=>T<cost i).card ≤ seeds.card := by
  let bad := seeds.filter fun i=>T<cost i
  have h : (T+1)*bad.card ≤ ∑ i ∈ seeds,cost i := by
    calc
      _ = ∑ _i ∈ bad,(T+1) := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ bad,cost i := by
        apply Finset.sum_le_sum
        intro i hi
        have h := (Finset.mem_filter.mp (show i∈seeds.filter (fun i=>T<cost i) from hi)).2
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset ..) (fun _ _ _=>Nat.zero_le _)
  have h' : (T+1)*(12*bad.card) ≤ (T+1)*seeds.card :=
    calc
      _ = 12*((T+1)*bad.card) := by ring
      _ ≤ 12*(∑ i ∈ seeds,cost i) := Nat.mul_le_mul_left 12 h
      _ ≤ _ := mean
  exact Nat.le_of_mul_le_mul_left h' (by omega)

def clipped (zero : R) (counted : Q→Bool) (T : ℕ) (tree : DecisionTree Q R) : DecisionTree Q R :=
  truncate T (mainOnly zero counted tree)

theorem clipped_agrees_on_actual_path (zero : R) (counted : Q→Bool) (oracle : Q→R)
    (freeConstant : ∀ q,counted q=false → oracle q=zero)
    (T : ℕ) (tree : DecisionTree Q R) (le : paid (mainCharge counted) oracle tree ≤ T) :
    evaluate oracle (clipped zero counted T tree)=evaluate oracle tree := by
  have E := elimination_exact zero counted oracle freeConstant tree
  exact (truncate_evaluate_of_paid_le T oracle _ (E.2.trans_le le)).trans E.1

theorem clipped_success (zero : R) (counted : Q→Bool) (oracle : Q→R)
    (freeConstant : ∀ q,counted q=false → oracle q=zero)
    (seeds : Finset Seed) (tree : Seed→DecisionTree Q R) (T : ℕ) (target : Bool)
    (good : 2*seeds.card ≤ 3*∑ i ∈ seeds,if evaluate oracle (tree i)=target then 1 else 0)
    (mean : 12*(∑ i ∈ seeds,paid (mainCharge counted) oracle (tree i)) ≤ (T+1)*seeds.card) :
    7*seeds.card ≤ 12*∑ i ∈ seeds,if evaluate oracle (clipped zero counted T (tree i))=target then 1 else 0 := by
  let cost := fun i=>paid (mainCharge counted) oracle (tree i)
  let orig := fun i=>if evaluate oracle (tree i)=target then (1:ℕ) else 0
  let clip := fun i=>if evaluate oracle (clipped zero counted T (tree i))=target then (1:ℕ) else 0
  have one (i : Seed) : orig i ≤ clip i+(if T<cost i then 1 else 0) := by
    by_cases hb : T<cost i
    · simp only [orig,clip,hb,if_true]
      split <;> split <;> omega
    · have h := clipped_agrees_on_actual_path zero counted oracle freeConstant T (tree i) (Nat.le_of_not_gt hb)
      simp only [orig,clip,h,if_neg hb,Nat.add_zero,Nat.le_refl]
  have loss := Finset.sum_le_sum (s:=seeds) (fun i _=>one i)
  have badEq : (∑ i ∈ seeds,if T<cost i then (1:ℕ) else 0)=(seeds.filter (fun i=>T<cost i)).card := by
    rw [Finset.card_filter]
  rw [Finset.sum_add_distrib,badEq] at loss
  have small := markov_cutoff seeds cost T mean
  change 2*seeds.card ≤ 3*∑ i ∈ seeds,orig i at good
  change 7*seeds.card ≤ 12*∑ i ∈ seeds,clip i
  omega

/-- The same finite off-support argument as R45, with success 7/12
instead of 2/3 to allow the loss incurred by clipping. -/
theorem weighted_capacity_seven [DecidableEq W] (zero : R) (oracle : W→Bool→Q→R)
    (support : Q→Finset W) (off : ∀ w b q,w∉support q → oracle w b q=zero)
    (capacity T : ℕ) (cap : ∀ q,(support q).card≤capacity)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (tree : Seed→DecisionTree Q R)
    (pool : Finset W)
    (bounded : ∀ i ∈ seeds,paid (fun _=>capacity) (fun _=>zero) (tree i)≤capacity*T)
    (success : ∀ w∈pool,∀ b : Bool,7*seeds.card≤
      12*∑ i ∈ seeds,if evaluate (oracle w b) (tree i)=b then 1 else 0) :
    pool.card ≤ 6*(capacity*T) := by
  have hl (w) (hw : w∈pool) : 14*seeds.card≤12*∑ i ∈ seeds,pairScore (tree i) oracle w := by
    simp only [pairScore,Finset.sum_add_distrib]
    have h0 := success w hw false
    have h1 := success w hw true
    omega
  have hL := Finset.sum_le_sum (s:=pool) hl
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hL
  rw [Finset.sum_comm (s:=pool) (t:=seeds)] at hL
  have hU : (∑ i ∈ seeds,∑ w ∈ pool,pairScore (tree i) oracle w) ≤ seeds.card*(pool.card+capacity*T) := by
    simpa using (Finset.sum_le_sum (s:=seeds) (fun i hi=>
      (score_sum_le zero oracle support off (fun _=>capacity) cap (tree i) pool).trans
        (Nat.add_le_add_left (bounded i hi) pool.card)) :
      (∑ i ∈ seeds,∑ w ∈ pool,pairScore (tree i) oracle w) ≤ ∑ _i ∈ seeds,(pool.card+capacity*T))
  have hC : seeds.card*(14*pool.card)≤seeds.card*(12*(pool.card+capacity*T)) := by
    calc
      _ = pool.card*(14*seeds.card) := by ring
      _ ≤ 12*(seeds.card*(pool.card+capacity*T)) := hL.trans (Nat.mul_le_mul_left 12 hU)
      _ = _ := by ring
  have h' := Nat.le_of_mul_le_mul_left hC (Finset.card_pos.mpr hs)
  omega

theorem capacity_at_cutoff [DecidableEq W] (zero : R) (oracle : W→Bool→Q→R)
    (support : Q→Finset W) (off : ∀ w b q,w∉support q → oracle w b q=zero)
    (counted : Q→Bool) (freeConstant : ∀ w b q,counted q=false → oracle w b q=zero)
    (capacity T : ℕ) (cap : ∀ q,(support q).card≤capacity)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (tree : Seed→DecisionTree Q R) (pool : Finset W)
    (mean : ∀ w∈pool,∀ b,12*(∑ i ∈ seeds,paid (mainCharge counted) (oracle w b) (tree i))≤(T+1)*seeds.card)
    (success : ∀ w∈pool,∀ b : Bool,2*seeds.card≤
      3*∑ i ∈ seeds,if evaluate (oracle w b) (tree i)=b then 1 else 0) :
    pool.card≤6*(capacity*T) := by
  apply weighted_capacity_seven zero oracle support off capacity T cap seeds hs
    (fun i=>clipped zero counted T (tree i)) pool
  · intro i _
    rw [paid_constant]
    exact Nat.mul_le_mul_left capacity (truncate_paid_le T _ _)
  · intro w hw b
    exact clipped_success zero counted (oracle w b) (freeConstant w b) seeds tree T b
      (success w hw b) (mean w hw b)

theorem mean_to_cutoff (n total : ℕ) (h : 0<n) :
    12*total ≤ ((12*total)/n+1)*n := by
  have div : (12*total)/n < (12*total)/n+1 := by omega
  exact (Nat.div_lt_iff_lt_mul h).mp div |>.le

theorem mean_bound_from_cutoff (n total B : ℕ) (h : B≤6*((12*total)/n)) :
    B*n≤72*total := by
  calc
    _ ≤ (6*((12*total)/n))*n := Nat.mul_le_mul_right n h
    _ = 6*(((12*total)/n)*n) := by ring
    _ ≤ 6*(12*total) := Nat.mul_le_mul_left 6 (Nat.div_mul_le_self _ _)
    _ = _ := by ring

#print axioms markov_cutoff
#print axioms clipped_agrees_on_actual_path
#print axioms clipped_success
#print axioms weighted_capacity_seven
#print axioms capacity_at_cutoff
#print axioms mean_to_cutoff
#print axioms mean_bound_from_cutoff
end J2R47Expected
