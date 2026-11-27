import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators
namespace HalfBlockCount

/-- First coordinates of opposite pairs at start -s, in a k-row half block. -/
def pairs (k s : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => i < s-i ∧ s-i < k

theorem pairs_as_interval (k s : ℕ) :
    pairs k s = Finset.Ico (s+1-k) (min k ((s+1)/2)) := by
  ext i
  simp [pairs]
  omega

theorem pairs_card (k s : ℕ) :
    (pairs k s).card = min k ((s+1)/2) - (s+1-k) := by
  rw [pairs_as_interval,Nat.card_Ico]

theorem first_odd (h j : ℕ) (hj : j < h) :
    (pairs (2*h) (2*j+1)).card = j+1 := by
  rw [pairs_card]; omega

theorem second_odd (h j : ℕ) (hj : j+1 < h) :
    (pairs (2*h) (4*h-2-(2*j+1))).card = j+1 := by
  rw [pairs_card]; omega

theorem first_even (h j : ℕ) (hj : j < h) :
    (pairs (2*h) (2*j)).card = j := by
  rw [pairs_card]; omega

theorem second_even (h j : ℕ) (hj : j < h) :
    (pairs (2*h) (4*h-2-2*j)).card = j := by
  rw [pairs_card]; omega

/-- Total excesses for the increasing half, after deleting the minority b. -/
theorem rising (b m : ℕ) :
    2*(∑ j ∈ Finset.range (b+m), (j+1-b)) = m*(m+1) := by
  induction m with
  | zero =>
    have hz : ∀ j ∈ Finset.range b, j+1-b = 0 := by
      intro j hj; have := Finset.mem_range.mp hj; omega
    simp [Finset.sum_eq_zero hz]
  | succ m ih =>
    rw [show b+(m+1)=b+m+1 by omega, Finset.sum_range_succ]
    have hv : b+m+1-b=m+1 := by omega
    rw [hv,Nat.mul_add,ih]
    ring

/-- The sum on the rising half without its central peak. -/
theorem rising_without_peak (b m : ℕ) :
    2*(∑ j ∈ Finset.range (b+m), (j-b)) + m = m*m := by
  induction m with
  | zero =>
    have hz : ∀ j ∈ Finset.range b, j-b=0 := by
      intro j hj; have := Finset.mem_range.mp hj; omega
    simp [Finset.sum_eq_zero hz]
  | succ m ih =>
    rw [show b+(m+1)=b+m+1 by omega, Finset.sum_range_succ,
      show b+m-b=m by omega,Nat.mul_add]
    nlinarith

theorem odd_multiplicity (b m : ℕ) :
    (∑ j ∈ Finset.range (b+m), (j+1-b)) +
    (∑ j ∈ Finset.range (b+m), (j-b)) = m^2 := by
  have h := rising b m
  have g := rising_without_peak b m
  nlinarith

theorem even_multiplicity (b m : ℕ) :
    2*(∑ j ∈ Finset.range (b+m), (j-b)) = m*(m-1) := by
  have h := rising_without_peak b m
  cases m with
  | zero => simpa using h
  | succ m =>
    simp only [Nat.succ_sub_one]
    nlinarith

/-- Sum over all odd or all even centers, including harmless empty end centers. -/
theorem all_centers (b m : ℕ) (eps : ℕ) (heps : eps ≤ 1) :
    (∑ j ∈ Finset.range (2*(b+m)), ((pairs (2*(b+m)) (2*j+eps)).card-b)) =
      if eps=1 then m^2 else m*(m-1) := by
  set h := b+m
  let f := fun j : ℕ => (pairs (2*h) (2*j+eps)).card-b
  change (∑ j ∈ Finset.range (2*h), f j) = _
  have low : (∑ j ∈ Finset.range h, f j) = ∑ j ∈ Finset.range h, (j+eps-b) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [f,pairs_card]
    omega
  have high : (∑ j ∈ Finset.range h, f (h+j)) = ∑ j ∈ Finset.range h, (j-b) := by
    rw [← Finset.sum_range_reflect (fun j : ℕ => j-b) h]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp only [f,pairs_card]
    omega
  rw [two_mul,Finset.sum_range_add,low,high]
  interval_cases eps
  · simp only [Nat.add_zero, Nat.zero_ne_one, if_false, ← two_mul]
    exact even_multiplicity b m
  · simp only [if_true]
    exact odd_multiplicity b m

#print axioms all_centers
#print axioms pairs_as_interval
#print axioms first_odd
#print axioms second_odd
#print axioms first_even
#print axioms second_even
#print axioms odd_multiplicity
#print axioms even_multiplicity
end HalfBlockCount
