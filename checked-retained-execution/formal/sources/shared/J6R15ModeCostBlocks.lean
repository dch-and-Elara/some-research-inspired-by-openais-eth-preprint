import J6R15ModeCostHead
import J6R15ModeCostHalfTail

/-! For q=1-1/(2k), use blocks of m=2k-1 weights. The head
costs at most 4^m and all tail blocks together cost at most 4^m.
Both estimates apply to finite products of arbitrary length. -/
namespace J6R15ModeCost
open scoped BigOperators

def biasedProduct (r : ℚ) (N : ℕ) : ℚ :=
  ∏ i ∈ Finset.range N,weightFactor r (i+1)

theorem rectangle_prod {A : Type*} [CommMonoid A] (f : ℕ→A) (m T : ℕ) :
    (∏ j ∈ Finset.range (m*T),f j) =
      (∏ t ∈ Finset.range T,∏ j ∈ Finset.range m,f (m*t+j)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.mul_succ,Finset.prod_range_add,Finset.prod_range_succ,ih]

theorem biasedProduct_nonneg (r : ℚ) (hr : 0≤r) (hR : r<1) (N : ℕ) :
    0≤biasedProduct r N := by
  unfold biasedProduct
  exact Finset.prod_nonneg (fun j _=>zero_le_one.trans
    (weightFactor_one_le r hr hR _ (Nat.succ_pos j)))

theorem biasedProduct_mono (r : ℚ) (hr : 0≤r) (hR : r<1) {N N' : ℕ} (H : N≤N') :
    biasedProduct r N≤biasedProduct r N' := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le H
  unfold biasedProduct
  rw [Finset.prod_range_add]
  apply le_mul_of_one_le_right
  · exact biasedProduct_nonneg r hr hR N
  · have ht : (∏ _ ∈ Finset.range e,(1:ℚ))≤
        (∏ i ∈ Finset.range e,weightFactor r (N+i+1)) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one)
        (fun i _ => weightFactor_one_le r hr hR _ (Nat.succ_pos _))
    simpa only [Finset.prod_const_one] using ht

theorem tailFactor (k t j : ℕ) (hk : 0<k) :
    weightFactor (dyadicBias k) (blockSize k*(t+1)+j+1) ≤
      (1-(1/2:ℚ)^(t+1))⁻¹ := by
  have ⟨hr,hR⟩ := dyadicBias_interval k hk
  have hm := bias_block_upper k hk
  have hP : dyadicBias k^(blockSize k*(t+1)+j+1)≤(1/2:ℚ)^(t+1) := by
    rw [Nat.add_assoc,pow_add,pow_mul]
    calc
      _≤((dyadicBias k)^blockSize k)^(t+1)*1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hR.le) (by positivity)
      _≤_ := by
        rw [mul_one]
        exact pow_le_pow_left₀ (by positivity) hm _
  refine inv_anti₀ ?_ (sub_le_sub_left hP 1)
  exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero t))

theorem tailBlocks (k T : ℕ) (hk : 0<k) :
    (∏ t ∈ Finset.range T,∏ j ∈ Finset.range (blockSize k),
      weightFactor (dyadicBias k) (blockSize k*(t+1)+j+1))≤(4:ℚ)^blockSize k := by
  have ⟨hr,hR⟩ := dyadicBias_interval k hk
  let a := fun t : ℕ => (1-(1/2:ℚ)^(t+1))⁻¹
  let m := blockSize k
  calc
    _≤∏ t ∈ Finset.range T,a t^m := by
      apply Finset.prod_le_prod
      · intro t _
        exact Finset.prod_nonneg (fun j _ => zero_le_one.trans
          (weightFactor_one_le _ hr.le hR _ (Nat.succ_pos _)))
      · intro t _
        have hh := Finset.prod_le_prod (s:=Finset.range m)
          (fun j _=>zero_le_one.trans (weightFactor_one_le _ hr.le hR _ (Nat.succ_pos _)))
          (fun j _=>tailFactor k t j hk)
        simpa only [Finset.prod_const,Finset.card_range] using hh
    _=(∏ t ∈ Finset.range T,a t)^m := Finset.prod_pow _ _ _
    _≤_ := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>inv_nonneg.mpr
      (sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))))) (halfTail_reciprocal T) _

theorem biasedProduct_uniform (k N : ℕ) (hk : 0<k) :
    biasedProduct (dyadicBias k) N≤(2:ℚ)^(8*k) := by
  have ⟨hr,hR⟩ := dyadicBias_interval k hk
  let m := blockSize k
  have hm : 1≤m := by unfold m blockSize; omega
  have hN : N≤m*(N+1) := by
    have H := Nat.mul_le_mul_right (N+1) hm
    rw [Nat.one_mul] at H
    omega
  refine (biasedProduct_mono _ hr.le hR hN).trans ?_
  unfold biasedProduct
  rw [rectangle_prod,Finset.prod_range_succ']
  simp only [Nat.mul_zero,Nat.zero_add]
  have hT := tailBlocks k N hk
  have hTN := Finset.prod_nonneg (s:=Finset.range N)
    (f:=fun t=>∏ j ∈ Finset.range m,weightFactor (dyadicBias k) (m*(t+1)+j+1))
    (fun t _=>Finset.prod_nonneg (fun j _=>zero_le_one.trans
      (weightFactor_one_le _ hr.le hR _ (Nat.succ_pos _))))
  have hA := mul_le_mul (finite_head k hk) hT hTN (by positivity)
  have hL : (4:ℚ)^m*(4:ℚ)^m≤(2:ℚ)^(8*k) := by
    rw [← pow_add,show (4:ℚ)=(2:ℚ)^2 by norm_num,← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    unfold m blockSize
    omega
  rw [mul_comm]
  exact hA.trans hL

#print axioms rectangle_prod
#print axioms tailFactor
#print axioms tailBlocks
#print axioms biasedProduct_uniform
end J6R15ModeCost


