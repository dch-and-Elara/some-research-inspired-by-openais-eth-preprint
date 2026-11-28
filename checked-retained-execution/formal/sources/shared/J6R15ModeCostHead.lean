import J6R15ModeCostGrouped
import J6R15ModeCostDyadic
import Mathlib.Data.Nat.Choose.Bounds

/-! A finite head bound via the exact central-binomial product. -/
namespace J6R15ModeCost
open scoped BigOperators

theorem head_factor (k j : ℕ) (hk : 0<k) (hj : 0<j) :
    weightFactor (dyadicBias k) j≤((blockSize k:ℚ)+j)/j := by
  let m : ℚ := blockSize k
  have hm : 0<m := by
    change (0:ℚ)<blockSize k
    exact_mod_cast (show 0<blockSize k by unfold blockSize; omega)
  have hJ : (0:ℚ)<j := by exact_mod_cast hj
  have hM : 0<m+j := by positivity
  have H : (j:ℚ)/(m+j)≤1-dyadicBias k^j := by
    have h := bias_power_fraction k hk j
    change dyadicBias k^j≤m/(m+j) at h
    have e : m/(m+j)+(j:ℚ)/(m+j)=1 := by
      rw [← add_div,div_self hM.ne']
    linarith
  have hh := inv_anti₀ (show (0:ℚ)<(j:ℚ)/(m+j) by positivity) H
  simpa only [weightFactor,inv_div] using hh

theorem shifted_ratio_choose (m n : ℕ) :
    (∏ i ∈ Finset.range n, ((m:ℚ)+i+1)/(i+1))=(Nat.choose (m+n) m:ℚ) := by
  induction n with
  | zero => simp [Nat.choose_self]
  | succ n ih =>
    rw [Finset.prod_range_succ,ih]
    have H := Nat.choose_mul_succ_eq (m+n) m
    rw [show m+n+1-m=n+1 by omega] at H
    have H' : ((m+n).choose m:ℚ)*((m:ℚ)+n+1)=((m+n+1).choose m:ℚ)*((n:ℚ)+1) := by
      exact_mod_cast H
    change ((m+n).choose m:ℚ)*(((m:ℚ)+n+1)/(n+1))=((m+n+1).choose m:ℚ)
    rw [← mul_div_assoc]
    exact (div_eq_iff (by positivity : (n:ℚ)+1≠0)).mpr H'

theorem finite_head (k : ℕ) (hk : 0<k) :
    (∏ i ∈ Finset.range (blockSize k),weightFactor (dyadicBias k) (i+1))≤(4:ℚ)^blockSize k := by
  let m := blockSize k
  calc
    _≤ ∏ i ∈ Finset.range m, ((m:ℚ)+i+1)/(i+1) := by
      apply Finset.prod_le_prod
      · intro j _
        exact zero_le_one.trans (weightFactor_one_le _ (dyadicBias_interval k hk).1.le
          (dyadicBias_interval k hk).2 _ (Nat.succ_pos j))
      · intro j _
        rw [add_assoc]
        simpa only [Nat.cast_add,Nat.cast_one] using head_factor k (j+1) hk (Nat.succ_pos j)
    _ = ((m+m).choose m:ℚ) := shifted_ratio_choose m m
    _ ≤ (4:ℚ)^m := by
      have H : ((m+m).choose m:ℚ)≤(2:ℚ)^(m+m) := by
        exact_mod_cast Nat.choose_le_two_pow (m+m) m
      rw [pow_add,← mul_pow] at H
      norm_num at H
      exact H

#print axioms head_factor
#print axioms shifted_ratio_choose
#print axioms finite_head
end J6R15ModeCost


