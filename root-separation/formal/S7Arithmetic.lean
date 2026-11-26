import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order

/-! The exact finite sums and inequalities in §7, over the rationals. -/
namespace S7
open Finset
open scoped BigOperators

theorem geometric (n : ℕ) :
    (∑ i ∈ range n, (1 : ℚ) / 2 ^ i) = 2 - 2 / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    ring

theorem firstMoment (n : ℕ) :
    (∑ i ∈ range (n + 1), (i : ℚ) / 2 ^ i) = 2 - (n + 2 : ℚ) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ, Nat.cast_succ]
    ring

theorem secondMoment (n : ℕ) :
    (∑ i ∈ range (n + 1), (i : ℚ)^2 / 2 ^ i) =
      6 - ((n : ℚ)^2 + 4*n + 6) / 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ, Nat.cast_succ]
    ring

/-- P.4, normalized by H L. -/
theorem clippedMass (v : ℕ) :
    (∑ i ∈ range v, ((v : ℚ) - i) / 2 ^ i) = 2*v - 2 + 2 / 2^v := by
  induction v with
  | zero => norm_num
  | succ v ih =>
    rw [sum_range_succ']
    have h : (∑ i ∈ range v, ((↑(v+1) : ℚ) - ↑(i+1)) / 2^(i+1)) =
        (∑ i ∈ range v, ((v : ℚ) - i) / 2^i) / 2 := by
      rw [sum_div]
      apply sum_congr rfl
      intro i _
      push_cast
      rw [pow_succ]
      ring
    rw [h, ih, pow_succ]
    push_cast
    ring

theorem clippedSurplus (H M L : ℚ) (v : ℕ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hv : M + 2*H ≤ H*v) :
    2*H*L + M ≤ H*L*(2*v - 2 + 2/2^v) - M*(2*L-1) := by
  have h1 := mul_le_mul_of_nonneg_right hv hL
  have hp : 0 ≤ H*L*(2 / (2 : ℚ)^v) := by positivity
  nlinarith only [h1, hp]

/-- P.5, finite loss before multiplication by H D_i. Includes the terminal term. -/
theorem clippedLoss (r n : ℕ) (h : r ≤ n) :
    (∑ j ∈ range (n+1), (j : ℚ) * (min j r : ℕ) / 2^j) =
      6 - (2*r+6 : ℚ)/2^r - (r : ℚ)*(n+2)/2^n := by
  induction n, h using Nat.le_induction with
  | base =>
    have he : (∑ j ∈ range (r+1), (j : ℚ) * (min j r : ℕ) / 2^j) =
        (∑ j ∈ range (r+1), (j : ℚ)^2 / 2^j) := by
      apply sum_congr rfl
      intro j hj
      rw [min_eq_left (by have := mem_range.mp hj; omega), pow_two]
    rw [he, secondMoment]
    ring
  | succ n hn ih =>
    rw [sum_range_succ, ih, min_eq_right (by omega), pow_succ, Nat.cast_succ]
    ring

/-- This is the exact cancellation used before P.6. -/
theorem clippedSlack (h H D : ℚ) (r n : ℕ) (hr : 1 ≤ r)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hcap : 6*H ≤ 8*h) :
    8*H*D/2^r ≤ 8*h*D - H*D*(6-(2*r+6 : ℚ)/2^r-(r : ℚ)*(n+2)/2^n) := by
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have h₁ := mul_le_mul_of_nonneg_right hcap hD
  have h₂ : 0 ≤ H*D*((r : ℚ)*(n+2)/2^n) := by positivity
  have h₃ : 0 ≤ H*D*((2*(r : ℚ)-2)/2^r) :=
    mul_nonneg (mul_nonneg hH hD) (div_nonneg (by linarith) (by positivity))
  calc
    _ ≤ 8*H*D/2^r + (8*h*D-6*H*D) + H*D*((r : ℚ)*(n+2)/2^n) +
        H*D*((2*(r : ℚ)-2)/2^r) := by linarith only [h₁,h₂,h₃]
    _ = _ := by ring

def envelope (r : ℕ) : ℚ := if r = 0 then 0 else ((r : ℚ)+2)/3

def kernel (j : ℕ) : ℚ := (j : ℚ)/2^(j+1)

/-- Exact super-solution slack in the recurrence following P.9. -/
theorem envelopeSlack (r : ℕ) (hr : 0 < r) :
    envelope r - 1 - (∑ j ∈ range r, kernel j * envelope (r-j)) =
      ((r : ℚ)-1)/(3*2^r) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hsum :
      (∑ j ∈ range (n+1), kernel j * envelope (n+1-j)) =
      ((n+3 : ℚ)*(∑ j ∈ range (n+1), (j : ℚ)/2^j) -
        (∑ j ∈ range (n+1), (j : ℚ)^2/2^j))/6 := by
    rw [sub_div, mul_sum, sum_div, sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [envelope, if_neg (by omega), Nat.cast_sub (by omega), kernel, pow_succ]
    push_cast
    ring
  rw [hsum, firstMoment, secondMoment, envelope, if_neg (by omega)]
  simp only [Nat.succ_eq_add_one, pow_succ]
  push_cast
  ring

theorem shellEnvelope (B : ℚ) (m : ℕ → ℚ) (v : ℕ) (hB : 0 ≤ B)
    (hstep : ∀ i < v, m i ≤ B + ∑ j ∈ range (v-i), kernel j * m (i+j)) :
    ∀ i < v, m i ≤ B * envelope (v-i) := by
  have step : ∀ r, ∀ i < v, v-i = r → m i ≤ B * envelope r := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro i hi hri
      have hr : 0 < r := by omega
      have hs := hstep i hi
      rw [hri] at hs
      refine hs.trans ?_
      calc
        _ ≤ B + ∑ j ∈ range r, kernel j * (B * envelope (r-j)) := by
          apply add_le_add_left
          apply sum_le_sum
          intro j hj
          by_cases h : j = 0
          · simp [h, kernel]
          · exact mul_le_mul_of_nonneg_left (ih (r-j) (by omega) (i+j)
                  (by have := mem_range.mp hj; omega) (by omega)) (by unfold kernel; positivity)
        _ ≤ B * envelope r := by
          have he := envelopeSlack r hr
          have hx : 0 ≤ ((r : ℚ)-1)/(3*2^r) := by
            have : (1:ℚ) ≤ r := by exact_mod_cast hr
            exact div_nonneg (sub_nonneg.mpr this) (by positivity)
          have hy : 1 + (∑ j ∈ range r, kernel j * envelope (r-j)) ≤ envelope r := by linarith
          convert mul_le_mul_of_nonneg_left hy hB using 1
          rw [mul_add, mul_one, mul_sum]
          congr 1
          apply sum_congr rfl
          intro j _
          ring
  exact fun i hi => step (v-i) i hi rfl

theorem shellMassBound (B : ℚ) (m : ℕ → ℚ) (v : ℕ) (hB : 0 ≤ B)
    (hstep : ∀ i < v, m i ≤ B + ∑ j ∈ range (v-i), kernel j * m (i+j)) :
    (∑ i ∈ range v, m i / 2^i) ≤ B/3*(2*v+2-2/2^v) := by
  calc
    _ ≤ ∑ i ∈ range v, (B * envelope (v-i)) / 2^i := by
      apply sum_le_sum
      intro i hi
      exact div_le_div_of_nonneg_right (shellEnvelope B m v hB hstep i (mem_range.mp hi)) (by positivity)
    _ = _ := by
      have he : (∑ i ∈ range v, (B * envelope (v-i)) / 2^i) =
          B/3 * ((∑ i ∈ range v, ((v : ℚ)-i)/2^i) + 2 * ∑ i ∈ range v, (1 : ℚ)/2^i) := by
        rw [mul_sum, ← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro i hi
        have := mem_range.mp hi
        rw [envelope, if_neg (by omega), Nat.cast_sub (by omega)]
        ring
      rw [he, clippedMass, geometric]
      ring

/-- Arithmetic part of P.9. K is the weighted shell average from P.8. -/
theorem averagedShellBound (h M D n a m higher K : ℚ)
    (hD : 0 < D)
    (hlower : 2*(D-1)*m - 4*M*n ≤ K)
    (hupper : K - D*higher ≤ 8*h*D+8*M*(a+1)) :
    2*m - higher ≤ 8*h+(8*M*(a+1)+4*M*n+2*m)/D := by
  have h' : 2*m-higher-8*h ≤ (8*M*(a+1)+4*M*n+2*m)/D :=
    (le_div_iff₀ hD).2 (by nlinarith only [hlower,hupper])
  linarith only [h']

end S7
