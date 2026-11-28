import J6R15ModeCostPotential

/-! Elementary rational parameter bounds for the packed mode product.
The parameter is 1-1/(2k), which gives a half bound in blocks of
2k-1 by Bernoulli, avoiding an analytic exponential estimate. -/
namespace J6R15ModeCost

def dyadicBias (k : ℕ) : ℚ := 1-1/(2*(k:ℚ))

def blockSize (k : ℕ) : ℕ := 2*k-1

theorem blockSize_cast (k : ℕ) (hk : 0<k) :
    (blockSize k:ℚ)=2*(k:ℚ)-1 := by
  unfold blockSize
  rw [Nat.cast_sub (by omega),Nat.cast_mul]
  norm_num

theorem dyadicBias_interval (k : ℕ) (hk : 0<k) :
    0<dyadicBias k ∧ dyadicBias k<1 := by
  have hk' : (0:ℚ)<k := by exact_mod_cast hk
  have ho : (1:ℚ)≤k := by exact_mod_cast hk
  have h₁ : (1:ℚ)/(2*k)<1 := by
    apply (div_lt_iff₀ (by positivity : (0:ℚ)<2*k)).mpr
    linarith
  have h₂ : (0:ℚ)<1/(2*k) := by positivity
  unfold dyadicBias
  exact ⟨by linarith,by linarith⟩

theorem bernoulli_pos (x : ℚ) (hx : 0≤x) (n : ℕ) :
    1+(n:ℚ)*x≤(1+x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    apply le_trans _ (mul_le_mul_of_nonneg_right ih (by linarith))
    have h := mul_nonneg (Nat.cast_nonneg n : (0:ℚ)≤n) (sq_nonneg x)
    nlinarith

theorem bernoulli_neg (x : ℚ) (hX : x≤1) (n : ℕ) :
    1-(n:ℚ)*x≤(1-x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    apply le_trans _ (mul_le_mul_of_nonneg_right ih (by linarith))
    have h := mul_nonneg (Nat.cast_nonneg n : (0:ℚ)≤n) (sq_nonneg x)
    nlinarith

theorem bias_inv (k : ℕ) (hk : 0<k) :
    (dyadicBias k)⁻¹=1+1/(blockSize k:ℚ) := by
  have hc : (0:ℚ)<k := by exact_mod_cast hk
  have h₁ : (0:ℚ)<blockSize k := by exact_mod_cast (show 0<blockSize k by unfold blockSize; omega)
  unfold dyadicBias
  rw [blockSize_cast k hk] at h₁ ⊢
  field_simp [hc.ne',h₁.ne']
  ring

theorem bias_k_lower (k : ℕ) (hk : 0<k) :
    (1/2:ℚ)≤dyadicBias k^k := by
  have hc : (0:ℚ)<k := by exact_mod_cast hk
  have q2 : (1:ℚ)/(2*k)≤1 := by
    have H := (dyadicBias_interval k hk).1
    unfold dyadicBias at H
    linarith
  have H := bernoulli_neg _ q2 k
  have hterm : (k:ℚ)*(1/(2*k))=1/2 := by
    field_simp [hc.ne']
  rw [hterm] at H
  change (1:ℚ)-1/2≤dyadicBias k^k at H
  linarith

theorem bias_power_fraction (k : ℕ) (hk : 0<k) (n : ℕ) :
    dyadicBias k^n ≤ (blockSize k:ℚ)/(blockSize k+n) := by
  let m : ℚ := blockSize k
  have hm : 0<m := by
    change (0:ℚ)<blockSize k
    exact_mod_cast (show 0<blockSize k by unfold blockSize; omega)
  have hN : 0<m+n := by positivity
  have V : 1+(n:ℚ)/m≤(dyadicBias k)⁻¹ ^ n := by
    rw [bias_inv k hk]
    change 1+(n:ℚ)/m≤(1+1/m)^n
    simpa only [div_eq_mul_inv,mul_one,one_mul] using
      (bernoulli_pos (1/m) (by positivity) n)
  have H := inv_anti₀ (show (0:ℚ)<1+(n:ℚ)/m by positivity) V
  have E : (1+(n:ℚ)/m)⁻¹=m/(m+n) := by
    field_simp [hm.ne',hN.ne']
  rw [← inv_pow,inv_inv,E] at H
  exact H

theorem bias_block_upper (k : ℕ) (hk : 0<k) :
    dyadicBias k^blockSize k≤(1/2:ℚ) := by
  have hm : 0<(blockSize k:ℚ) := by
    exact_mod_cast (show 0<blockSize k by unfold blockSize; omega)
  refine (bias_power_fraction k hk (blockSize k)).trans_eq ?_
  field_simp [hm.ne']
  ring

#print axioms bernoulli_pos
#print axioms bernoulli_neg
#print axioms bias_k_lower
#print axioms bias_power_fraction
#print axioms bias_block_upper
end J6R15ModeCost


