import BooleanCube.SymmetricDegree
import Mathlib.Data.Nat.Periodic

namespace LocalReconstruction

private theorem tail_telescoping (q l : ℕ) (hl : l ≤ q) :
    ∑ k ∈ Finset.range (l+1), ((q:ℝ)-2*k)*q.choose k =
      ((q:ℝ)-l)*q.choose l := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq q l)
    push_cast [Nat.cast_sub (by omega : l ≤ q)] at h
    rw [Finset.sum_range_succ, ih (by omega)]
    push_cast
    linear_combination -h

private theorem tail_cost {q l : ℕ} (hl : 2*l < q) :
    ((q:ℝ)-2*l) * (∑ k ∈ Finset.range l, (q.choose k:ℝ)) ≤
      (q:ℝ)*q.choose l := by
  have h : 2*(l:ℝ) < q := by exact_mod_cast hl
  calc
    _ ≤ ∑ k ∈ Finset.range (l+1), ((q:ℝ)-2*l)*q.choose k := by
      rw [Finset.mul_sum, Finset.sum_range_succ]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h.le) (Nat.cast_nonneg _))
    _ ≤ ∑ k ∈ Finset.range (l+1), ((q:ℝ)-2*k)*q.choose k := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : (k:ℝ) ≤ l := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = ((q:ℝ)-l)*q.choose l := tail_telescoping q l (by omega)
    _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

private theorem cheap_residue (q l h : ℕ) (hh : 0 < h) :
    ∃ r < h, ∑ k ∈ (Finset.range l).filter (fun k => k % h = r), (q.choose k:ℝ) ≤
      (∑ k ∈ Finset.range l, (q.choose k:ℝ)) / h := by
  let cost (r : ℕ) := ∑ k ∈ (Finset.range l).filter (fun k => k % h = r), (q.choose k:ℝ)
  have hs : ∑ r ∈ Finset.range h, cost r = ∑ k ∈ Finset.range l, (q.choose k:ℝ) := by
    exact Finset.sum_fiberwise_of_maps_to
      (fun k _ => Finset.mem_range.mpr (Nat.mod_lt k hh)) _
  have hc : (h:ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have ht : ∑ r ∈ Finset.range h, cost r ≤
      ∑ _ ∈ Finset.range h, (∑ k ∈ Finset.range l, (q.choose k:ℝ)) / h := by
    rw [hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hc]
  obtain ⟨r, hr, hb⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hh⟩ ht
  exact ⟨r, Finset.mem_range.mp hr, hb⟩

private theorem interval_has_residue (L : ℕ) {h r : ℕ} (hr : r < h) :
    ∃ k, L ≤ k ∧ k < L+h ∧ k % h = r := by
  let p := fun k : ℕ => k % h = r
  have period : Function.Periodic p h := fun k => congrArg (· = r) (Nat.add_mod_right k h)
  have hc := Nat.filter_Ico_card_eq_of_periodic L h p period
  have pos : 0 < h.count p := by
    rw [Nat.count_eq_card_filter_range]
    exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hr, Nat.mod_eq_of_lt hr⟩⟩
  rw [← hc] at pos
  obtain ⟨k, hk⟩ := Finset.card_pos.mp pos
  exact ⟨k, (Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).1,
    (Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).2, (Finset.mem_filter.mp hk).2⟩

/-- Delete the central pair and a cheapest periodic class in each reflected tail. -/
theorem symmetric_periodic_layers {q l : ℕ} (hl : 2*l < q) :
    ∃ K : Finset ℕ, K ⊆ Finset.range (q+1) ∧ maxGap q K ≤ q-2*l ∧
      (∑ k ∈ K, (q.choose k:ℝ)) ≤
        2*(q.choose l:ℝ)*(1+(q:ℝ)/((q:ℝ)-2*l)^2) := by
  let h := q-2*l
  have hh : 0 < h := by dsimp [h]; omega
  have hh' : (h:ℝ) = (q:ℝ)-2*l := by
    dsimp [h]; rw [Nat.cast_sub (by omega : 2*l ≤ q)]; push_cast; rfl
  obtain ⟨r, hr, hb⟩ := cheap_residue q l h hh
  let T := (Finset.range l).filter fun k => k % h = r
  let R := T.image (fun k => q-k)
  let K := insert l (insert (q-l) (T ∪ R))
  have hT : ∀ k ∈ T, k < l := fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hR : ∀ k ∈ R, q-l < k ∧ k ≤ q := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have := hT j hj
    omega
  have hkL : l ∈ K := Finset.mem_insert_self _ _
  have hkR : q-l ∈ K := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  refine ⟨K, ?_, (maxGap_le_iff _ _ _).mpr ?_, ?_⟩
  · intro k hk
    apply Finset.mem_range.mpr
    simp only [K, Finset.mem_insert, Finset.mem_union] at hk
    rcases hk with rfl | rfl | ht | ht
    · omega
    · omega
    · have := hT k ht; omega
    · have := (hR k ht).2; omega
  · intro L U hLU hU hclear
    change U-L ≤ h
    by_contra! hlong
    have skipL : l < L ∨ U < l := by
      by_contra! hn
      exact hclear l hn.1 hn.2 hkL
    have skipR : q-l < L ∨ U < q-l := by
      by_contra! hn
      exact hclear (q-l) hn.1 hn.2 hkR
    rcases skipL with hleft | hleft
    · rcases skipR with hright | hright
      · obtain ⟨j, hj₁, hj₂, hj₃⟩ := interval_has_residue (q-U) hr
        have hj : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          dsimp [h] at hlong hj₂; omega), hj₃⟩
        exact hclear (q-j) (by omega) (by omega)
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))))
      · dsimp [h] at hlong
        omega
    · obtain ⟨j, hj₁, hj₂, hj₃⟩ := interval_has_residue L hr
      have hj : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj₃⟩
      exact hclear j hj₁ (by omega)
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hj)))
  · have hrSum : ∑ k ∈ R, (q.choose k:ℝ) = ∑ k ∈ T, (q.choose k:ℝ) := by
      unfold R
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl fun k hk => by rw [Nat.choose_symm (by have := hT k hk; omega)]
      · intro a ha b hb hab
        change q-a = q-b at hab
        have := hT a ha
        have := hT b hb
        omega
    have hn₁ : q-l ∉ T ∪ R := by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun hm => by have := hT _ hm; omega, fun hm => by have := (hR _ hm).1; omega⟩
    have hn₂ : l ∉ insert (q-l) (T ∪ R) := by
      simp only [Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨by omega, fun hm => by have := hT _ hm; omega,
        fun hm => by have := (hR _ hm).1; omega⟩
    have hd : Disjoint T R := Finset.disjoint_left.mpr fun k ht hx => by
      have := hT k ht
      have := (hR k hx).1
      omega
    have hc : 0 < (h:ℝ) := by exact_mod_cast hh
    have hTail : ∑ k ∈ T, (q.choose k:ℝ) ≤ (q:ℝ)*q.choose l/(h:ℝ)^2 := by
      apply hb.trans
      apply (div_le_div_iff₀ hc (sq_pos_of_pos hc)).mpr
      have ht := tail_cost (q := q) (l := l) hl
      rw [← hh'] at ht
      nlinarith only [mul_le_mul_of_nonneg_right ht hc.le]
    dsimp only [K]
    rw [Finset.sum_insert hn₂, Finset.sum_insert hn₁, Finset.sum_union hd, hrSum,
      Nat.choose_symm (by omega : l ≤ q), ← hh']
    linarith only [hTail, show (q:ℝ)*q.choose l/(h:ℝ)^2 = q.choose l*((q:ℝ)/(h:ℝ)^2) by ring]

/-- A retained interval with degree below half the cube dimension has two bounding
deleted layers around the central cut. -/
theorem symmetric_central_pair {q d : ℕ} {K : Finset ℕ}
    (hK : K ⊆ Finset.range (q+1)) (hg : maxGap q K ≤ d) (hd : d+2 < q/2) :
    ∃ l ∈ K, ∃ r ∈ K, l ≤ q/2 ∧ q/2 < r ∧ r ≤ q ∧ r-l ≤ d+2 := by
  let L := K.filter (· ≤ q/2)
  let R := K.filter (q/2 < ·)
  have gap := (maxGap_le_iff _ _ _).mp hg
  have hL : L.Nonempty := by
    by_contra h
    have b := gap 0 (q/2) (by omega) (by omega) fun k _ hk hm =>
      h ⟨k, Finset.mem_filter.mpr ⟨hm, hk⟩⟩
    omega
  have hR : R.Nonempty := by
    by_contra h
    have b := gap (q/2+1) q (by omega) le_rfl fun k hk _ hm =>
      h ⟨k, Finset.mem_filter.mpr ⟨hm, by omega⟩⟩
    omega
  let l := L.max' hL
  let r := R.min' hR
  have hl := Finset.mem_filter.mp (Finset.max'_mem L hL)
  have hr := Finset.mem_filter.mp (Finset.min'_mem R hR)
  have hrq := Finset.mem_range.mp (hK hr.1)
  refine ⟨l, hl.1, r, hr.1, hl.2, hr.2, by omega, ?_⟩
  have hlMid : l ≤ q/2 := hl.2
  have hrMid : q/2 < r := hr.2
  by_contra! h
  have b := gap (l+1) (r-1) (by omega) (by omega) (fun k hk₁ hk₂ hm => by
    by_cases hk : k ≤ q/2
    · have := Finset.le_max' L k (Finset.mem_filter.mpr ⟨hm, hk⟩)
      change k ≤ l at this
      omega
    · have := Finset.min'_le R k (Finset.mem_filter.mpr ⟨hm, by omega⟩)
      change r ≤ k at this
      omega)
  omega

end LocalReconstruction
