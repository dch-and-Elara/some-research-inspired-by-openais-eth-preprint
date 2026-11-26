import HermiteLossReflection
import DenominatorBudget

/-! Coordinatewise finite-error transfer over the actual two-local ring. -/
namespace HermiteLoss
open P1DyadicGrid DenominatorBudget

theorem int_power_rat (i : ℕ) : (pow₂ i : ℚ)=(2:ℚ)^i := by simp [pow₂]

theorem scaled_ratio_integral (num den : ℤ) (hn : num≠0) (hd : den≠0)
    (k : ℕ) (loss : level den ≤ k+level num) :
    (2:ℚ)^k*((num:ℚ)/(den:ℚ)) ∈ twoLocalSubalgebra := by
  obtain ⟨n, hon, heN⟩ := integer_odd_factor hn
  obtain ⟨d, hod, heD⟩ := integer_odd_factor hd
  have hN : (num:ℚ)=(2:ℚ)^level num*(n:ℚ) := by
    change num=pow₂ (level num)*n at heN
    simpa only [Int.cast_mul,int_power_rat] using congrArg (fun x : ℤ => (x:ℚ)) heN
  have hD : (den:ℚ)=(2:ℚ)^level den*(d:ℚ) := by
    change den=pow₂ (level den)*d at heD
    simpa only [Int.cast_mul,int_power_rat] using congrArg (fun x : ℤ => (x:ℚ)) heD
  let j := k+level num-level den
  have hj : k+level num = j+level den := (Nat.sub_add_cancel loss).symm
  apply (mem_twoLocal_iff _).2
  refine ⟨pow₂ j*n,d,?_,?_⟩
  · exact (Int.not_even_iff_odd.mpr hod) ∘ even_iff_two_dvd.mpr
  · have hdq : (d:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hod
    rw [hN,hD, Int.cast_mul,int_power_rat]
    calc
      _ = ((2:ℚ)^(k+level num)*(n:ℚ))/((2:ℚ)^level den*d) := by rw [pow_add]; ring
      _ = _ := by rw [hj,pow_add]; field_simp

theorem level_pow₂ (i : ℕ) : level (pow₂ i)=i := by
  simpa only [mul_one] using valuation_pow₂_mul_odd i (by decide : Odd (1:ℤ))

theorem slope_factor_integral {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈grid a) (hne : t≠q) :
    (2:ℚ)^(a+1)/(t-q:ℤ) ∈ twoLocalSubalgebra := by
  have he := scaled_ratio_integral 1 (t-q) (by decide) (sub_ne_zero.mpr hne) (a+1)
    (by have h := level_difference_le ht hq hne; omega)
  simpa only [Int.cast_one, mul_one_div] using he

def congruence (p : ℕ) (x y : ℚ) : Prop :=
  ∃ r ∈ twoLocalSubalgebra, x-y=(2:ℚ)^p*r

theorem weight_precision_transfer {p prec k : ℕ} {w x y : ℚ}
    (scale : (2:ℚ)^k*w ∈ twoLocalSubalgebra)
    (fit : p+k≤prec) (data : congruence prec x y) :
    congruence p (w*x) (w*y) := by
  rcases data with ⟨r,hr,he⟩
  let z := prec-(p+k)
  have hz : prec=p+z+k := by dsimp [z]; omega
  have ht : (2:ℚ)^z ∈ twoLocalSubalgebra :=
    (mem_twoLocal_iff _).2 ⟨(2:ℤ)^z,1,by norm_num,by simp⟩
  refine ⟨(2:ℚ)^z*(((2:ℚ)^k*w)*r),
    twoLocalSubalgebra.mul_mem ht (twoLocalSubalgebra.mul_mem scale hr),?_⟩
  rw [← mul_sub,he,hz,pow_add,pow_add]
  ring

#print axioms scaled_ratio_integral
#print axioms slope_factor_integral
#print axioms weight_precision_transfer
end HermiteLoss

