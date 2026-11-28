import J1PPrintedMain

/-! Exact correspondence of executable square-root roundings with the
floor and ceiling notation printed in the source. -/

namespace J1PPrinted

theorem ceilSqrt_le_iff (lambda c : ℕ) : ceilSqrt lambda ≤ c ↔ lambda ≤ c^2 := by
  unfold ceilSqrt
  by_cases h : lambda.sqrt^2=lambda
  · rw [if_pos h, Nat.add_zero]
    constructor
    · intro hc
      exact h.symm.le.trans (Nat.pow_le_pow_left hc _)
    · intro hc
      exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : (2:ℕ)≠0)).mp
        (h.le.trans hc)
  · rw [if_neg h]
    constructor
    · intro hc
      exact ((Nat.sqrt_lt'.mp (show lambda.sqrt<c by omega))).le
    · intro hc
      by_contra! hn
      have ho : c≤lambda.sqrt := by omega
      have he := le_antisymm ((Nat.sqrt_le' lambda)) (hc.trans (Nat.pow_le_pow_left ho 2))
      exact h he

theorem ceilSqrt_is_original (lambda : ℕ) : ceilSqrt lambda = ⌈Real.sqrt (lambda:ℝ)⌉₊ := by
  have hcmp (c : ℕ) : ceilSqrt lambda ≤ c ↔ ⌈Real.sqrt (lambda:ℝ)⌉₊ ≤ c := by
    rw [ceilSqrt_le_iff, Nat.ceil_le, Real.sqrt_le_iff]
    constructor
    · intro h
      exact ⟨by positivity, by exact_mod_cast h⟩
    · intro h
      exact_mod_cast h.2
  exact le_antisymm ((hcmp _).mpr le_rfl) ((hcmp _).mp le_rfl)

theorem alphabet_is_original (lambda : ℕ) (hnu : 0 < J1PhysicalPrinted.sourceNu lambda) :
    J1PhysicalPrinted.sourceR lambda =
      ⌊Real.sqrt (lambda:ℝ) / (J1PhysicalPrinted.sourceNu lambda : ℝ)^2⌋₊ := by
  let nu := J1PhysicalPrinted.sourceNu lambda
  have hnu0 : (0:ℝ)<nu := by exact_mod_cast hnu
  have hcmp (c : ℕ) : c ≤ J1PhysicalPrinted.sourceR lambda ↔
      c ≤ ⌊Real.sqrt (lambda:ℝ) / (nu:ℝ)^2⌋₊ := by
    change c≤lambda.sqrt/nu^2 ↔ _
    rw [Nat.le_div_iff_mul_le (pow_pos hnu _), Nat.le_sqrt',
      Nat.le_floor_iff (by positivity), le_div_iff₀ (by positivity),
      Real.le_sqrt (by positivity) (by positivity)]
    constructor <;> intro h <;> exact_mod_cast h
  exact le_antisymm ((hcmp _).mp le_rfl) ((hcmp _).mpr le_rfl)

#print axioms ceilSqrt_is_original
#print axioms alphabet_is_original

end J1PPrinted

