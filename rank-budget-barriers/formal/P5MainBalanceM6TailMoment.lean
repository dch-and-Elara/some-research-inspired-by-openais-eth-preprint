import P5MainBalanceM6PrintedSchedule

/-! Finite, elementary moment bound. It uses only the installed real
exponential estimate, not a probability-space or extra measure axiom. -/
namespace P5MainBalance.M6
open Real
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [Nonempty A]

theorem exp_centered_indicator_bound (x p t : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hp0 : 0≤p) (hp1 : p≤1) (ht : |t|≤1) :
    exp (t*(x-p))≤1+t*(x-p)+t^2 := by
  have hd : |x-p|≤1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hMul : |t*(x-p)|≤|t| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hd
  have hp2 : (t*(x-p))^2≤t^2 := by
    rw [←sq_abs (t*(x-p)),←sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg _) hMul 2
  have hh := (abs_exp_sub_one_sub_id_le (hMul.trans ht)).trans hp2
  linarith only [le_trans (le_abs_self (exp (t*(x-p))-1-t*(x-p))) hh]

theorem axis_moment_of_sum (f : A→ℝ) (p t : ℝ)
    (hf : ∀ x,0≤f x ∧ f x≤1) (hp0 : 0≤p) (hp1 : p≤1)
    (hs : (∑ x,f x)=(Fintype.card A:ℝ)*p) (ht : |t|≤1) :
    (∑ x,exp (t*(f x-p)))≤(Fintype.card A:ℝ)*exp (t^2) := by
  calc
    _ ≤ ∑ x : A,(1+t*(f x-p)+t^2) :=
      Finset.sum_le_sum (fun x _=>exp_centered_indicator_bound (f x) p t (hf x).1 (hf x).2 hp0 hp1 ht)
    _ = (Fintype.card A:ℝ)*(1+t^2) := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,
        nsmul_eq_mul,Finset.card_univ,hs]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [add_one_le_exp (t^2)]) (by positivity)

variable {I : Type*} [Fintype I]

set_option maxHeartbeats 7000000 in
theorem word_moment_of_sum (f : A→ℝ) (p t : ℝ)
    (hf : ∀ x,0≤f x ∧ f x≤1) (hp0 : 0≤p) (hp1 : p≤1)
    (hs : (∑ x,f x)=(Fintype.card A:ℝ)*p) (ht : |t|≤1) :
    (∑ u : I→A,exp (t*((∑ i,f (u i))-(Fintype.card I:ℝ)*p))) ≤
      (Fintype.card (I→A):ℝ)*exp ((Fintype.card I:ℝ)*t^2) := by
  have hterm (u : I→A) :
      exp (t*((∑ i,f (u i))-(Fintype.card I:ℝ)*p)) =
        ∏ i,exp (t*(f (u i)-p)) := by
    rw [←exp_sum]
    congr 1
    simp only [←Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  have hB := axis_moment_of_sum f p t hf hp0 hp1 hs ht
  simp_rw [hterm]
  rw [←Fintype.prod_sum (fun (_i : I) x=>exp (t*(f x-p)))]
  calc
    _ ≤ ∏ _i : I,((Fintype.card A:ℝ)*exp (t^2)) := by
      apply Finset.prod_le_prod
      · exact fun _ _=>Finset.sum_nonneg (fun _ _=>exp_nonneg _)
      · exact fun _ _=>hB
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,mul_pow,
        ←exp_nat_mul]

#print axioms exp_centered_indicator_bound
#print axioms axis_moment_of_sum
#print axioms word_moment_of_sum
end P5MainBalance.M6
