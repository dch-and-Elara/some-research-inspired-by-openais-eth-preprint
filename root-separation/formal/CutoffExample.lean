import RootProgram

namespace FourthPaperReview

private theorem shell_log (k : ℕ) : S11.lambda (7 * 2^k) = k+3 := by
  have hpos : 0 < (2:ℕ)^k := pow_pos (by decide) _
  have hlo : 2^(k+2) < 7*2^k := by
    rw [pow_add, Nat.mul_comm (2^k)]
    exact Nat.mul_lt_mul_of_pos_right (by decide : 2^2 < 7) hpos
  have hhi : 7*2^k ≤ 2^(k+3) := by
    rw [pow_add, Nat.mul_comm (2^k)]
    exact Nat.mul_le_mul_right _ (by decide : 7 ≤ 2^3)
  have lower := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hlo
  have upper := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hhi
  unfold S11.lambda
  omega

-- N = 2^131072, s = 7N/2. The root bound applies with K = 0.
-- The asymptotic source estimate lambda^(4/5) <= u fails at this size.
theorem source_parameter_example :
    S11.lambda (7 * 2^131071) = 131074 ∧
    S11.retained (7 * 2^131071) 0 = 1 ∧
    (S11.retained (7 * 2^131071) 0)^5 < (S11.lambda (7 * 2^131071))^4 := by
  simp only [S11.retained, shell_log]
  decide

#print axioms source_parameter_example
end FourthPaperReview