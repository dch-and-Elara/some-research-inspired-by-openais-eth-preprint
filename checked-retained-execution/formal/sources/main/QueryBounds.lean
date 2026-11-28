
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import FiniteWeightedQueryTree

namespace FiniteWeightedQueryTree
open scoped BigOperators

variable {Q R W Seed : Type*} [DecidableEq W]

/-- Union of the supports visited along the all-zero reply path. -/
def zeroCover (zero : R) (support : Q → Finset W) : DecisionTree Q R → Finset W
  | .leaf _ => ∅
  | .ask q next => support q ∪ zeroCover zero support (next zero)

theorem zeroCover_card_le (zero : R) (support : Q → Finset W)
    (cost : Q → ℕ) (cap : ∀ q, (support q).card ≤ cost q) (tree : DecisionTree Q R) :
    (zeroCover zero support tree).card ≤ paid cost (fun _ => zero) tree := by
  induction tree with
  | leaf _ => simp [zeroCover, paid]
  | ask q next ih =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (cap q) (ih zero))

theorem evaluate_eq_zeroPath (zero : R)
    (oracle : W → Bool → Q → R) (support : Q → Finset W)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (tree : DecisionTree Q R) (w : W) (b : Bool)
    (hw : w ∉ zeroCover zero support tree) :
    evaluate (oracle w b) tree = evaluate (fun _ => zero) tree := by
  induction tree with
  | leaf _ => rfl
  | ask q next ih =>
    simp only [zeroCover, Finset.mem_union, not_or] at hw
    simpa only [evaluate, off w b q hw.1] using ih zero hw.2

/-- Number of correct answers on the two witnesses associated with the word. -/
def pairScore (tree : DecisionTree Q R) (oracle : W → Bool → Q → R) (w : W) : ℕ :=
  (if evaluate (oracle w false) tree = false then 1 else 0) +
  (if evaluate (oracle w true) tree = true then 1 else 0)

theorem pairScore_le (zero : R) (oracle : W → Bool → Q → R)
    (support : Q → Finset W)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (tree : DecisionTree Q R) (w : W) :
    pairScore tree oracle w ≤ 1 + if w ∈ zeroCover zero support tree then 1 else 0 := by
  by_cases h : w ∈ zeroCover zero support tree
  · simp only [pairScore, if_pos h]; split <;> split <;> omega
  · rw [pairScore, if_neg h, evaluate_eq_zeroPath zero oracle support off tree w false h,
      evaluate_eq_zeroPath zero oracle support off tree w true h]
    cases evaluate (fun _ => zero) tree <;> decide

theorem score_sum_le (zero : R) (oracle : W → Bool → Q → R)
    (support : Q → Finset W) (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (cost : Q → ℕ) (cap : ∀ q, (support q).card ≤ cost q)
    (tree : DecisionTree Q R) (pool : Finset W) :
    ∑ w ∈ pool, pairScore tree oracle w ≤
      pool.card + paid cost (fun _ => zero) tree := by
  classical
  calc
    _ ≤ ∑ w ∈ pool, (1 + if w ∈ zeroCover zero support tree then 1 else 0) :=
      Finset.sum_le_sum fun w _ => pairScore_le zero oracle support off tree w
    _ = pool.card + (pool.filter fun w => w ∈ zeroCover zero support tree).card := by
      rw [Finset.sum_add_distrib, Finset.card_filter]
      simp
    _ ≤ _ := Nat.add_le_add_left
      ((Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)).trans
        (zeroCover_card_le zero support cost cap tree)) _

/-- Bounded-error J2 for uniform finite seeds (rational distributions can be replicated).
    The budget applies to the zero path; a separate truncation bridges actual-run budgets. -/
theorem randomized_weighted_capacity (zero : R) (oracle : W → Bool → Q → R)
    (support : Q → Finset W) (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (cost : Q → ℕ) (cap : ∀ q, (support q).card ≤ cost q)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (tree : Seed → DecisionTree Q R)
    (pool : Finset W) (budget : ℕ)
    (bounded : ∀ s ∈ seeds, paid cost (fun _ => zero) (tree s) ≤ budget)
    (success : ∀ w ∈ pool, ∀ b : Bool,
      2 * seeds.card ≤
        3 * ∑ s ∈ seeds, (if evaluate (oracle w b) (tree s) = b then 1 else 0)) :
    pool.card ≤ 3 * budget := by
  classical
  have hl (w) (hw : w ∈ pool) :
      4 * seeds.card ≤ 3 * ∑ s ∈ seeds, pairScore (tree s) oracle w := by
    simp only [pairScore, Finset.sum_add_distrib]
    have h0 := success w hw false
    have h1 := success w hw true
    omega
  have hL := Finset.sum_le_sum (s := pool) hl
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hL
  rw [Finset.sum_comm (s := pool) (t := seeds)] at hL
  have hU : (∑ s ∈ seeds, ∑ w ∈ pool, pairScore (tree s) oracle w) ≤
      seeds.card * (pool.card + budget) := by
    simpa using (Finset.sum_le_sum (s := seeds) (fun s hs' =>
      (score_sum_le zero oracle support off cost cap (tree s) pool).trans
        (Nat.add_le_add_left (bounded s hs') pool.card)) :
      (∑ s ∈ seeds, ∑ w ∈ pool, pairScore (tree s) oracle w) ≤
        ∑ _s ∈ seeds, (pool.card + budget))
  have hC : seeds.card * pool.card ≤ seeds.card * (3 * budget) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hC (Finset.card_pos.mpr hs)

/-- Stop immediately before the request that would exceed the query limit. -/
def truncate : ℕ → DecisionTree Q R → DecisionTree Q R
  | 0, .leaf b => .leaf b
  | 0, .ask _ _ => .leaf false
  | _+1, .leaf b => .leaf b
  | n+1, .ask q next => .ask q (fun r => truncate n (next r))

theorem truncate_paid_le (n : ℕ) (oracle : Q → R) (tree : DecisionTree Q R) :
    paid (fun _ => 1) oracle (truncate n tree) ≤ n := by
  induction n generalizing tree with
  | zero => cases tree <;> simp [truncate, paid]
  | succ n ih =>
    cases tree with
    | leaf b => simp [truncate, paid]
    | ask q next =>
      have h := ih (next (oracle q))
      simp only [truncate, paid]
      omega

theorem truncate_evaluate_of_paid_le (n : ℕ) (oracle : Q → R) (tree : DecisionTree Q R)
    (h : paid (fun _ => 1) oracle tree ≤ n) :
    evaluate oracle (truncate n tree) = evaluate oracle tree := by
  induction n generalizing tree with
  | zero => cases tree <;> simp_all [truncate, paid, evaluate]
  | succ n ih =>
    cases tree with
    | leaf b => rfl
    | ask q next =>
      simp only [truncate, evaluate]
      apply ih
      simp only [paid] at h
      omega

theorem randomized_query_capacity (zero : R) (oracle : W → Bool → Q → R)
    (support : Q → Finset W) (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (capacity : ℕ) (cap : ∀ q, (support q).card ≤ capacity)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (tree : Seed → DecisionTree Q R)
    (pool : Finset W) (limit : ℕ)
    (bounded : ∀ s ∈ seeds, ∀ w ∈ pool, ∀ b, paid (fun _ => 1) (oracle w b) (tree s) ≤ limit)
    (success : ∀ w ∈ pool, ∀ b : Bool, 2 * seeds.card ≤
        3 * ∑ s ∈ seeds, (if evaluate (oracle w b) (tree s) = b then 1 else 0)) :
    pool.card ≤ 3 * (capacity * limit) := by
  apply randomized_weighted_capacity zero oracle support off (fun _ => capacity) cap
    seeds hs (fun s => truncate limit (tree s)) pool (capacity * limit)
  · intro s _
    rw [paid_constant]
    exact Nat.mul_le_mul_left _ (truncate_paid_le limit _ _)
  · intro w hw b
    have hh : (∑ s ∈ seeds, (if evaluate (oracle w b) (truncate limit (tree s)) = b then 1 else 0)) =
        ∑ s ∈ seeds, (if evaluate (oracle w b) (tree s) = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s hs'
      rw [truncate_evaluate_of_paid_le _ _ _ (bounded s hs' w hw b)]
    rw [hh]
    exact success w hw b

#print axioms randomized_query_capacity
#print axioms zeroCover_card_le
#print axioms score_sum_le

/-- J2 weighted mixed count. Constant D replies have empty support and cost zero. -/
theorem mixed_actual_path {Complete Group D : Type*} {k free : ℕ}
    (zero : R)
    (oracle : (Fin k → Bool) → Bool → (Complete ⊕ Group ⊕ D) → R)
    (sC : Complete → Finset (Fin k → Bool)) (sG : Group → Finset (Fin k → Bool))
    (hC : ∀ q, (sC q).card ≤ 1) (hG : ∀ q, (sG q).card ≤ 2 ^ free)
    (offC : ∀ w b q, w ∉ sC q → oracle w b (.inl q) = zero)
    (offG : ∀ w b q, w ∉ sG q → oracle w b (.inr (.inl q)) = zero)
    (offD : ∀ w b q, oracle w b (.inr (.inr q)) = zero)
    (t : DecisionTree (Complete ⊕ Group ⊕ D) R)
    (h : ∀ w b, evaluate (oracle w b) t = b) :
    ∃ w b, 2 ^ k ≤
      paid (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2 ^ free) (fun _ => 0))) (oracle w b) t := by
  classical
  let S : Complete ⊕ Group ⊕ D → Finset (Fin k → Bool) :=
    Sum.elim sC (Sum.elim sG (fun _ => ∅))
  apply bit_pattern_capacity zero oracle S _ _ _ t h
  · intro w b q hq
    rcases q with q | q
    · exact offC w b q hq
    · rcases q with q | q
      · exact offG w b q hq
      · exact offD w b q
  · intro q
    rcases q with q | q
    · exact hC q
    · rcases q with q | q
      · exact hG q
      · simp [S]

#print axioms mixed_actual_path

end FiniteWeightedQueryTree


