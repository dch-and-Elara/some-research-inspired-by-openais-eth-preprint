import P5PrecisionOptEnergy
import P5P3ShellRecurrence

/-! Finite reverse recurrence after the pointwise shell inequality.
The cutoff is an actual zero tail, not the use of a common choice
within nonzero shells. -/
namespace Paper5.PrecisionOpt
open scoped BigOperators

theorem half_weight_reindex (j : ℕ) :
    ((j+1:ℕ):ℚ)/(2:ℚ)^(j+1)=2*Paper5.P3.shellWeight j := by
  unfold Paper5.P3.shellWeight
  push_cast
  rw [pow_succ (2:ℚ) (j+1)]
  field_simp

theorem shell_tail_reindex (m : ℕ→ℚ) {u v i : ℕ} (hi : i<v) (hv : v≤u)
    (hcut : ∀ k,v ≤ k → m k=0) :
    (∑ k∈Finset.range u,((k-i:ℕ):ℚ)/(2:ℚ)^(k-i)*m k) =
      2*∑ j∈Finset.range (v-i-1),Paper5.P3.shellWeight j*m (i+j+1) := by
  have hh : (∑ k∈Finset.range v,((k-i:ℕ):ℚ)/(2:ℚ)^(k-i)*m k) =
      ∑ k∈Finset.range u,((k-i:ℕ):ℚ)/(2:ℚ)^(k-i)*m k := by
    apply Finset.sum_subset (Finset.range_mono hv)
    intro k _ hk
    rw [hcut k (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))),mul_zero]
  rw [←hh]
  conv_lhs => rw [show v=(i+1)+(v-i-1) by omega,Finset.sum_range_add]
  have hz : (∑ k∈Finset.range (i+1),((k-i:ℕ):ℚ)/(2:ℚ)^(k-i)*m k)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hp : k-i=0 := by have := Finset.mem_range.mp hk; omega
    simp [hp]
  rw [hz,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h : i+1+j-i=j+1 := by omega
  rw [h,half_weight_reindex,show i+1+j=i+j+1 by omega,mul_assoc]

theorem finite_backward_means (m : ℕ→ℚ) {u v : ℕ} (hv : v≤u) (B : ℚ) (hB : 0≤B)
    (hn : ∀ k,0≤m k) (hcut : ∀ k,v ≤ k → m k=0)
    (hrec : ∀ i, i < v → 2*m i-(∑ k∈Finset.range u,((k-i:ℕ):ℚ)/(2:ℚ)^(k-i)*m k)≤2*B) :
    ∀ i, i < v → m i ≤ B*((v-i:ℕ)+2:ℚ)/3 := by
  let g (n : ℕ) := if n<v then m (v-(n+1)) else 0
  have hg_nonnegative (n : ℕ) : 0≤g n := by
    by_cases h : n<v
    · simpa only [g,if_pos h] using hn (v-(n+1))
    · simp [g,h]
  have hg_rec (n : ℕ) :
      g n ≤ B+∑ j∈Finset.range n,Paper5.P3.shellWeight j*g (n-(j+1)) := by
    by_cases ht : n<v
    · let i := v-(n+1)
      have hi : i<v := by dsimp [i]; omega
      have hp : v-i-1=n := by dsimp [i]; omega
      have H := hrec i hi
      rw [shell_tail_reindex m hi hv hcut,hp] at H
      have hs : (∑ j∈Finset.range n,Paper5.P3.shellWeight j*g (n-(j+1))) =
          ∑ j∈Finset.range n,Paper5.P3.shellWeight j*m (i+j+1) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hlt := Finset.mem_range.mp hj
        have he : n-(j+1)<v := by omega
        have hval : v-(n-(j+1)+1)=i+j+1 := by dsimp [i]; omega
        simp only [g,if_pos he,hval]
      rw [hs,show g n=m i by simp [g,ht,i]]
      linarith
    · have hg0 : g n=0 := by simp [g,ht]
      rw [hg0]
      exact add_nonneg hB (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (by unfold Paper5.P3.shellWeight; positivity) (hg_nonnegative _)))
  intro i hi
  let r := v-i-1
  have hr : r<v := by dsimp [r]; omega
  have hr' : v-(r+1)=i := by dsimp [r]; omega
  have hBnd := Paper5.P3.backward_shell_envelope B hB g hg_rec r
  rw [show g r=m i by simp only [g,if_pos hr,hr']] at hBnd
  have he : ((r:ℚ)+3) = ((v-i:ℕ):ℚ)+2 := by
    have hN : r+1=v-i := by dsimp [r]; omega
    have hR : ((r+1:ℕ):ℚ)=((v-i:ℕ):ℚ) := congrArg (fun x : ℕ => (x:ℚ)) hN
    push_cast at hR
    linarith
  rwa [he] at hBnd

def shellAffineMass (v : ℕ) : ℚ :=
  ∑ i∈Finset.range v,((v:ℚ)-i+2)/(2:ℚ)^i

theorem shellAffineMass_closed (v : ℕ) :
    shellAffineMass v=2*(v:ℚ)+2-2/(2:ℚ)^v := by
  induction v with
  | zero => norm_num [shellAffineMass]
  | succ v ih =>
    have h : shellAffineMass (v+1)=shellAffineMass v+
        (∑ j∈Finset.range v,(1:ℚ)/2^j)+3/(2:ℚ)^v := by
      unfold shellAffineMass
      rw [Finset.sum_range_succ,←Finset.sum_add_distrib]
      push_cast
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    rw [h,ih,dyadic_reciprocal_sum,pow_succ]
    push_cast
    field_simp
    ring

theorem reverse_mean_totals (m : ℕ→ℚ) (v : ℕ) (B : ℚ) (hB : 0≤B)
    (hm : ∀ i, i < v → m i≤B*((v-i:ℕ)+2:ℚ)/3) :
    (∑ i∈Finset.range v,m i/(2:ℚ)^i)≤B/3*(2*(v:ℚ)+2) := by
  have h : (∑ i∈Finset.range v,m i/(2:ℚ)^i)≤B/3*shellAffineMass v := by
    unfold shellAffineMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hu := Finset.mem_range.mp hi
    have H := div_le_div_of_nonneg_right (hm i hu) (by positivity : 0≤(2:ℚ)^i)
    rw [Nat.cast_sub hu.le] at H
    exact H.trans_eq (by ring)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [shellAffineMass_closed]
  linarith [show (0:ℚ)≤2/(2:ℚ)^v by positivity]

#print axioms shell_tail_reindex
#print axioms finite_backward_means
#print axioms shellAffineMass_closed
#print axioms reverse_mean_totals
end Paper5.PrecisionOpt
