import P5MainBalanceM6TailMoment

/-! Two-sided quantitative product-word tail. Only uniform finite
cardinalities and exact exponentials appear in the statement. -/
namespace P5MainBalance.M6
open Real
open scoped BigOperators Classical

variable {S : Type*} [Fintype S] [Nonempty S]

theorem exp_markov_finite (Z : S→ℝ) (t a C : ℝ) (ht : 0≤t)
    (hm : (∑ u,exp (t*Z u))≤(Fintype.card S:ℝ)*exp C) :
    ((Finset.univ.filter (fun u=>a≤Z u)).card:ℝ)/(Fintype.card S:ℝ)
      ≤exp (C-t*a) := by
  let H := Finset.univ.filter (fun u=>a≤Z u)
  have hS : 0<(Fintype.card S:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card S)
  have h₁ : (H.card:ℝ)*exp (t*a)≤∑ u∈H,exp (t*Z u) := by
    rw [←nsmul_eq_mul,←Finset.sum_const]
    apply Finset.sum_le_sum
    intro x hx
    exact exp_le_exp_of_le (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 ht)
  have h₂ : (∑ u∈H,exp (t*Z u))≤∑ u,exp (t*Z u) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _=>exp_nonneg (t*Z u))
  have h := (le_div_iff₀ (exp_pos (t*a))).mpr (h₁.trans (h₂.trans hm))
  change (H.card:ℝ)/(Fintype.card S:ℝ)≤exp (C-t*a)
  rw [exp_sub]
  apply (div_le_iff₀ hS).mpr
  convert h using 1
  ring

theorem two_sided_markov_finite (Z : S→ℝ) (t a C : ℝ) (ht : 0≤t)
    (hp : (∑ u,exp (t*Z u))≤(Fintype.card S:ℝ)*exp C)
    (hm : (∑ u,exp ((-t)*Z u))≤(Fintype.card S:ℝ)*exp C) :
    ((Finset.univ.filter (fun u=>a≤|Z u|)).card:ℝ)/(Fintype.card S:ℝ)
      ≤2*exp (C-t*a) := by
  let H := Finset.univ.filter (fun u=>a≤Z u)
  let K := Finset.univ.filter (fun u=>a≤ -Z u)
  have he : (Finset.univ.filter (fun u=>a≤|Z u|))=H∪K := by
    ext u
    simp only [H,K,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    by_cases h : 0≤Z u
    · rw [abs_of_nonneg h]
      exact ⟨Or.inl,fun h' => h'.elim id (fun t=>by linarith only [h,t])⟩
    · have hz : Z u≤0 := (lt_of_not_ge h).le
      rw [abs_of_nonpos hz]
      exact ⟨Or.inr,fun h' => h'.elim (fun v=>by linarith only [hz,v]) id⟩
  have hH := exp_markov_finite Z t a C ht hp
  have hK := exp_markov_finite (fun u=> -Z u) t a C ht (by simpa only [mul_neg,neg_mul] using hm)
  rw [he]
  calc
    _ ≤ ((H.card:ℝ)+(K.card:ℝ))/(Fintype.card S:ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_union_le H K
    _ = _ + _ := add_div _ _ _
    _ ≤ _ := by
      have h := add_le_add hH hK
      simpa only [two_mul,H,K] using h

variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A]

set_option maxHeartbeats 7000000 in
theorem word_two_sided_tail (f : A→ℝ) (p t a : ℝ)
    (hf : ∀ x,0≤f x ∧ f x≤1) (hp0 : 0≤p) (hp1 : p≤1)
    (hs : (∑ x,f x)=(Fintype.card A:ℝ)*p) (ht0 : 0≤t) (ht1 : t≤1) :
    ((Finset.univ.filter (fun u : I→A=>a≤|(∑ i,f (u i))-(Fintype.card I:ℝ)*p|)).card:ℝ) /
      (Fintype.card (I→A):ℝ)≤2*exp ((Fintype.card I:ℝ)*t^2-t*a) := by
  apply two_sided_markov_finite _ _ _ _ ht0
  · exact word_moment_of_sum f p t hf hp0 hp1 hs (by rw [abs_of_nonneg ht0]; exact ht1)
  · simpa only [neg_sq] using
      (word_moment_of_sum f p (-t) hf hp0 hp1 hs (by rw [abs_neg,abs_of_nonneg ht0]; exact ht1) :
        (∑ u : I→A,exp ((-t)*((∑ i,f (u i))-(Fintype.card I:ℝ)*p)))≤
          (Fintype.card (I→A):ℝ)*exp ((Fintype.card I:ℝ)*(-t)^2))

#print axioms exp_markov_finite
#print axioms two_sided_markov_finite
#print axioms word_two_sided_tail
end P5MainBalance.M6
