import HalfBridge
import GrenetStrict

open Round4Transfer

namespace GrenetRational

theorem strict_square : StrictSquareStatement := by
  intro z hz n e he
  exact GrenetStrict.prefix_det_ne_zero_of_den_gt_two z hz e he

/-- The exact normalized prefix length over Q for every rational start. -/
theorem normalized_prefix_exact (z : ℚ) (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (normalizedPrefix z m) t ↔ threshold z t ≤ m :=
  normalized_prefix_iff_of_branches strict_square half_obstruction z t m ht

/-- Theorem 1.2. The ratio equation is in R, the normalized threshold is
computed in Q, and both directions concern exact evaluation in R. -/
theorem rational_ratio_exact {R : Type*} [CommRing R] [Nontrivial R]
    [IsAddTorsionFree R] (a b : R) (A : ℤ) (B : ℕ) (hB : 0 < B)
    (hb : b ∈ nonZeroDivisors R) (hRatio : (B : R)*a = (A : R)*b)
    (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (ringPrefix a b m) t ↔ threshold (A / (B : ℚ)) t ≤ m :=
  rational_ratio_exact_of_branches strict_square half_obstruction
    a b A B hB hb hRatio t m ht

theorem rational_ratio_least {R : Type*} [CommRing R] [Nontrivial R]
    [IsAddTorsionFree R] (a b : R) (A : ℤ) (B : ℕ) (hB : 0 < B)
    (hb : b ∈ nonZeroDivisors R) (hRatio : (B : R)*a = (A : R)*b)
    (t : ℕ) (ht : 1 ≤ t) :
    IsLeast {m : ℕ | DeterminesUnboundedSparse (ringPrefix a b m) t}
      (threshold (A / (B : ℚ)) t) := by
  refine ⟨(rational_ratio_exact a b A B hB hb hRatio t _ ht).mpr le_rfl, ?_⟩
  intro m hm
  exact (rational_ratio_exact a b A B hB hb hRatio t m ht).mp hm

theorem rational_progression_exact (a b : ℚ) (hb : b ≠ 0) (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (ringPrefix a b m) t ↔ threshold (a / b) t ≤ m := by
  let z := a/b
  have hz : (z.num : ℚ)/(z.den : ℚ) = z := z.num_div_den
  have hZ : (z.den : ℚ)*z = z.num := by
    calc
      _ = (z.den : ℚ)*((z.num : ℚ)/(z.den : ℚ)) := congrArg (fun q : ℚ => (z.den : ℚ)*q) hz.symm
      _ = _ := by rw [mul_comm, div_mul_cancel₀ _ (by exact_mod_cast z.den_ne_zero : (z.den : ℚ) ≠ 0)]
  have hab : (z.den : ℚ)*a = (z.num : ℚ)*b := by
    have he := congrArg (fun r : ℚ => r*b) hZ
    change ((z.den : ℚ)*(a/b))*b = _ at he
    rwa [mul_assoc, div_mul_cancel₀ _ hb] at he
  rw [← show (z.num : ℚ)/(z.den : ℚ) = a/b from hz]
  exact rational_ratio_exact a b z.num z.den z.den_pos
    (mem_nonZeroDivisors_iff_ne_zero.mpr hb) hab t m ht


/-- The threshold in the literal floor/ceiling form of Theorem 1.2. -/
theorem rational_ratio_exact_manuscript {R : Type*} [CommRing R] [Nontrivial R]
    [IsAddTorsionFree R] (a b : R) (A : ℤ) (B : ℕ) (hB : 0 < B)
    (hb : b ∈ nonZeroDivisors R) (hRatio : (B : R)*a = (A : R)*b)
    (t m : ℕ) (ht : 1 ≤ t) :
    let z := (A : ℚ)/(B : ℚ)
    DeterminesUnboundedSparse (ringPrefix a b m) t ↔
      (if 2 < z.den then 2*t else
        if 2*t ≤ (⌈-z⌉ : ℤ).toNat then 2*t else 2*t + (⌊-z⌋+1 : ℤ).toNat) ≤ m := by
  change DeterminesUnboundedSparse (ringPrefix a b m) t ↔ _
  rw [rational_ratio_exact a b A B hB hb hRatio t m ht]
  simp only [threshold, signThreshold, negativeLength, firstPositive, Nat.add_comm]

theorem threshold_one_eq (z : ℚ) : threshold z 1 = GrenetPaper.oneTermLength z := by
  apply Nat.le_antisymm
  · apply (normalized_prefix_exact z 1 _ le_rfl).mp
    exact (GrenetPaper.rational_one_term_prefix_exact z _).mpr le_rfl
  · apply (GrenetPaper.rational_one_term_prefix_exact z _).mp
    exact (normalized_prefix_exact z 1 _ le_rfl).mpr le_rfl
end GrenetRational
