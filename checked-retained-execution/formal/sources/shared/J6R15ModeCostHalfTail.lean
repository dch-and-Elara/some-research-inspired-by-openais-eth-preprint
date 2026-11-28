import J6R15ModeCostPotential
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A uniform finite dyadic product bound. The first term is 1/2;
the tail product is at least one minus its total deleted mass, at
least 1/2 again. No convergence or analytic infinite product. -/
namespace J6R15ModeCost
open scoped BigOperators

theorem comp_prod_lower {I : Type*} (s : Finset I) (f : I→ℚ)
    (hf : ∀ i∈s,0≤f i ∧ f i≤1) :
    1-(∑ i ∈ s,f i)≤(∏ i ∈ s,(1-f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hA := hf a (Finset.mem_insert_self a s)
    have hS : ∀ i∈s,0≤f i ∧ f i≤1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : 0≤∑ i∈s,f i := Finset.sum_nonneg (fun i hi => (hS i hi).1)
    have hx := mul_nonneg hA.1 hsum
    rw [Finset.sum_insert ha,Finset.prod_insert ha]
    calc
      _≤(1-f a)*(1-∑ i∈s,f i) := by nlinarith
      _≤_ := mul_le_mul_of_nonneg_left (ih hS) (sub_nonneg.mpr hA.2)

theorem halfTail_sum (n : ℕ) :
    (∑ i ∈ Finset.range n,(1/2:ℚ)^(i+2))=(1/2:ℚ)*(1-(1/2:ℚ)^n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,pow_succ (1/2:ℚ) n,pow_add (1/2:ℚ) n 2]
    ring

theorem halfTail_product (n : ℕ) :
    (1/4:ℚ) ≤ (∏ i ∈ Finset.range n,(1-(1/2:ℚ)^(i+1))) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [Finset.prod_range_succ']
    have bound : (1/2:ℚ)≤(∏ i ∈ Finset.range n,(1-(1/2:ℚ)^(i+2))) := by
      have H := comp_prod_lower (Finset.range n) (fun i => (1/2:ℚ)^(i+2))
        (fun i _ => ⟨by positivity,pow_le_one₀ (by norm_num) (by norm_num)⟩)
      rw [halfTail_sum n] at H
      have hu : (0:ℚ)≤(1/2:ℚ)^n := by positivity
      linarith
    have hs := mul_le_mul_of_nonneg_left bound (show (0:ℚ)≤1/2 by norm_num)
    convert hs using 1 <;> norm_num [Nat.add_assoc,mul_comm]

theorem halfTail_reciprocal (n : ℕ) :
    (∏ i ∈ Finset.range n,(1-(1/2:ℚ)^(i+1))⁻¹)≤4 := by
  let f := fun i : ℕ => 1-(1/2:ℚ)^(i+1)
  change (∏ i ∈ Finset.range n,(f i)⁻¹)≤4
  have hP (i : ℕ) : 0<f i :=
    sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero i))
  have hQ := Finset.prod_nonneg (s:=Finset.range n) (f:=fun i=>(f i)⁻¹)
    (fun i _ => (inv_pos.mpr (hP i)).le)
  have H : (∏ i ∈ Finset.range n,f i)*(∏ i ∈ Finset.range n,(f i)⁻¹)=1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => mul_inv_cancel₀ (hP i).ne')
  have h := mul_le_mul_of_nonneg_right (halfTail_product n) hQ
  change (1/4:ℚ)*(∏ i ∈ Finset.range n,(f i)⁻¹)≤
    (∏ i ∈ Finset.range n,f i)*(∏ i ∈ Finset.range n,(f i)⁻¹) at h
  rw [H] at h
  linarith

#print axioms comp_prod_lower
#print axioms halfTail_product
#print axioms halfTail_reciprocal
end J6R15ModeCost



