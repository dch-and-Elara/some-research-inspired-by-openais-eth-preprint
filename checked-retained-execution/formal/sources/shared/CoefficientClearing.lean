
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace CoefficientClearing
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Explicit denominator product for an actual finite target allocation list.
    It is not assumed that the terms in the sum share a reduced denominator. -/
theorem clear_target_sum (s : Finset ι) (a d : ι → ℤ)
    (hd : ∀ i ∈ s, d i ≠ 0) :
    ((∏ i ∈ s, d i : ℤ) : ℚ) *
        (∑ i ∈ s, (a i : ℚ) / d i) =
      ((∑ i ∈ s, a i * ∏ j ∈ s.erase i, d j : ℤ) : ℚ) := by
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hdi : (d i : ℚ) ≠ 0 := by exact_mod_cast hd i hi
  have he : (∏ j ∈ s.erase i, (d j : ℚ)) * d i = ∏ j ∈ s, (d j : ℚ) :=
    Finset.prod_erase_mul _ _ hi
  rw [← he]
  field_simp

theorem product_odd (s : Finset ι) (d : ι → ℤ)
    (h : ∀ i ∈ s, Odd (d i)) :
    Odd (∏ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [DecidableEq ι] in
theorem sum_abs_upper (s : Finset ι) (a : ι → ℤ) (B : ℤ)
    (h : ∀ i ∈ s, |a i| ≤ B) :
    |∑ i ∈ s, a i| ≤ s.card * B := by
  calc
    _ ≤ ∑ i ∈ s, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = _ := by simp

omit [DecidableEq ι] in
/-- Precise finite counterpart of the numerator bit-size argument:
    per-term budget e and at most 2^k terms suffice when e+k < prec−1. -/
theorem centered_after_sum (prec e k : ℕ) (s : Finset ι) (a : ι → ℤ)
    (hs : s.card ≤ 2 ^ k) (ha : ∀ i ∈ s, |a i| ≤ 2 ^ e)
    (hprec : e + k + 1 < prec) :
    (∑ i ∈ s, a i) * 2 ∈ Set.Ioc (-((2 : ℤ) ^ prec)) ((2 : ℤ) ^ prec) := by
  have hcard : (s.card : ℤ) ≤ (2 : ℤ)^k := by exact_mod_cast hs
  have h := (sum_abs_upper s a ((2:ℤ)^e) ha).trans
    (mul_le_mul_of_nonneg_right hcard (by positivity))
  rw [← pow_add] at h
  have he : (2 : ℤ)^(k+e+1) < (2 : ℤ)^prec :=
    pow_lt_pow_right₀ (by decide) (by omega)
  rw [pow_succ] at he
  have hpos := le_abs_self (∑ i ∈ s, a i)
  have hneg := neg_le_abs (∑ i ∈ s, a i)
  constructor <;> linarith

#print axioms clear_target_sum
#print axioms product_odd
#print axioms sum_abs_upper
#print axioms centered_after_sum
end CoefficientClearing

