
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace AdaptiveState
open scoped BigOperators

/-- Each node uses a history-relative alphabet of at most 2^b replies.
    Impossible replies are explicitly absent via a finset of feasible labels. -/
inductive Tree (O : Type*) where
  | leaf (value : O)
  | ask (b : ℕ) (feasible : Finset (Fin (2 ^ b))) (next : Fin (2 ^ b) → Tree O)

variable {O : Type*} [DecidableEq O]

def outputs : Tree O → Finset O
  | .leaf o => {o}
  | .ask _ feasible next => feasible.biUnion fun r => outputs (next r)

def Bounded : Tree O → ℕ → Prop
  | .leaf _, _ => True
  | .ask b feasible next, B => b ≤ B ∧ ∀ r ∈ feasible, Bounded (next r) (B - b)

theorem card_outputs (t : Tree O) (B : ℕ) (h : Bounded t B) :
    (outputs t).card ≤ 2 ^ B := by
  induction t generalizing B with
  | leaf v =>
    simpa [outputs] using (Nat.one_le_pow B 2 (by decide))
  | ask b feasible next ih =>
    obtain ⟨hb, hc⟩ := h
    calc
      (outputs (.ask b feasible next)).card ≤
          ∑ r ∈ feasible, (outputs (next r)).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ feasible, 2 ^ (B - b) := Finset.sum_le_sum fun r hr => ih r _ (hc r hr)
      _ = feasible.card * 2 ^ (B - b) := by simp
      _ ≤ 2 ^ b * 2 ^ (B - b) := Nat.mul_le_mul_right _
        (by simpa using Finset.card_le_univ feasible)
      _ = 2 ^ B := by rw [← pow_add, Nat.add_sub_of_le hb]

/-- Integer-bit form of A5. The two state alphabets have caps 2^B, 2^b.
    For noninteger rate/cost one needs the real-valued mass argument instead. -/
theorem menu_state_output_bound {Menu State : Type*} [DecidableEq Menu] [DecidableEq State]
    (menus : Finset Menu) (states : Menu → Finset State) (t : Menu → State → Tree O)
    (B b K : ℕ) (hM : menus.card ≤ 2 ^ B)
    (hS : ∀ m ∈ menus, (states m).card ≤ 2 ^ b)
    (hT : ∀ m ∈ menus, ∀ s ∈ states m, Bounded (t m s) K) :
    (menus.biUnion fun m => (states m).biUnion fun s => outputs (t m s)).card ≤
      2 ^ (B + b + K) := by
  classical
  have one (m) (hm : m ∈ menus) :
      ((states m).biUnion fun s => outputs (t m s)).card ≤ 2 ^ b * 2 ^ K := by
    calc
      _ ≤ ∑ s ∈ states m, (outputs (t m s)).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ states m, 2 ^ K :=
        Finset.sum_le_sum fun s hs => card_outputs (t m s) K (hT m hm s hs)
      _ = (states m).card * 2 ^ K := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (hS m hm)
  calc
    _ ≤ ∑ m ∈ menus, ((states m).biUnion fun s => outputs (t m s)).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ menus, 2 ^ b * 2 ^ K := Finset.sum_le_sum one
    _ = menus.card * (2 ^ b * 2 ^ K) := by simp
    _ ≤ 2 ^ B * (2 ^ b * 2 ^ K) := Nat.mul_le_mul_right _ hM
    _ = _ := by rw [← Nat.mul_assoc, ← pow_add, ← pow_add]

/-- An unrounded history tree. The branch count is exact; unlike the bit
    specialization it need not be a power of two. A feasible reply partition
    can omit any impossible labels before a node is built. -/
inductive FanTree (O : Type*) where
  | leaf (value : O)
  | ask (branches : ℕ) (next : Fin branches → FanTree O)

def fanOutputs : FanTree O → Finset O
  | .leaf v => {v}
  | .ask _ next => Finset.univ.biUnion fun j => fanOutputs (next j)

/-- The product of branching factors on every terminal path is at most T.
    This is an unrounded form of the conditional log-alphabet budget. -/
def FanBound : FanTree O → ℚ → Prop
  | .leaf _, T => 1 ≤ T
  | .ask n next, T => 0 ≤ T ∧ ∀ j, FanBound (next j) (T / n)

theorem fan_card (t : FanTree O) (T : ℚ) (h : FanBound t T) :
    ((fanOutputs t).card : ℚ) ≤ T := by
  induction t generalizing T with
  | leaf v => simpa [fanOutputs] using h
  | ask n next ih =>
    obtain ⟨hT, hchildren⟩ := h
    by_cases hn : n = 0
    · subst n; simpa [fanOutputs] using hT
    · have hq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      calc
        _ ≤ ∑ j : Fin n, ((fanOutputs (next j)).card : ℚ) := by
          exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)))
            (t := fun j => fanOutputs (next j)))
        _ ≤ ∑ _j : Fin n, T / n := Finset.sum_le_sum fun j _ => ih j _ (hchildren j)
        _ = (n : ℚ) * (T / n) := by simp
        _ = T := mul_div_cancel₀ _ hq

#print axioms fan_card

#print axioms card_outputs
#print axioms menu_state_output_bound
end AdaptiveState

