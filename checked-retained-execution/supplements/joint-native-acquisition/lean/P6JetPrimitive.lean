import P6Joint
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped Polynomial BigOperators Classical
open Polynomial

namespace P6Joint
noncomputable section

variable {K I : Type*} [CommRing K] [DecidableEq I]

theorem anchored_product_expand (s : Finset I) (a b : I → K[X]) :
    (∏ i ∈ s, (a i + X * b i)) =
    ∑ t ∈ s.powerset, X^t.card * ((∏ i ∈ t, b i) * ∏ i ∈ s \ t, a i) := by
  simp_rw [add_comm (a _) (X * _)]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_mul_distrib, Finset.prod_const, mul_assoc]

theorem anchored_coeff_small (s : Finset I) (a b : I → K[X]) (j : ℕ) :
    ((∏ i ∈ s, (a i + X * b i))).coeff j =
    ∑ t ∈ s.powerset.filter (fun t => t.card ≤ j),
      ((∏ i ∈ t, b i) * ∏ i ∈ s \ t, a i).coeff (j-t.card) := by
  rw [anchored_product_expand, Polynomial.finset_sum_coeff, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  rw [Polynomial.coeff_X_pow_mul']

/-- A term of the normalized singleton series is invisible whenever
its known dyadic order, including the probe's own valuation, exhausts
the receiver precision. Works without requiring the probe-unit factor
to actually be a unit. -/
theorem normalized_tail_term_zero {K : Type*} [CommRing K]
    (p v s j : ℕ) (u c : K) (hp : (2 : K)^p = 0)
    (order : p ≤ v+s+(1+s)*j) :
    (2:K)^v * ((2:K)^s*u) * (2*((2:K)^s*u))^j * c = 0 := by
  have h : 2 * ((2:K)^s*u) = (2:K)^(1+s)*u := by
    rw [pow_add, pow_one, mul_assoc]
  rw [h, mul_pow, ← pow_mul]
  have hh :
      (2:K)^v * ((2:K)^s*u) * ((2:K)^((1+s)*j)*u^j) * c =
      (2:K)^(v+s+(1+s)*j) * (u*u^j*c) := by
    rw [pow_add, pow_add]
    ring
  rw [hh, ← Nat.add_sub_of_le order, pow_add, hp, zero_mul, zero_mul]

#print axioms normalized_tail_term_zero

#print axioms anchored_product_expand
#print axioms anchored_coeff_small
end
end P6Joint
