import LogarithmicBudget

/-!
# Exceeding each polynomial power

For a positive rational t, a lower bound (tN)² ≤ 320 log₂(N) d² makes
2^d exceed N^p for each fixed natural p. The integer cutoff is explicit.
-/

namespace PowerCost

/-- Round up the fixed coefficient in the logarithmic tail estimate. -/
def multiplier (t : ℚ) (p : ℕ) : ℕ := ⌈320 * ((p : ℚ) + 1) ^ 2 / t ^ 2⌉₊

def threshold (t : ℚ) (p : ℕ) : ℕ :=
  LogarithmicBudget.cutoff (multiplier t p) 1

/-- The squared lower bound on d forces it past the binary logarithm of
N^p, with slack for the upper rounding of the logarithm. -/
theorem exponent_exceeds_log (t : ℚ) (N d p : ℕ) (ht : 0 < t)
    (hsquare : (t * N) ^ 2 ≤ 320 * (N.log2 : ℚ) * (d : ℚ) ^ 2)
    (hsize : threshold t p ≤ N) : (p + 1) * (N.log2 + 1) < d := by
  let C := multiplier t p
  have hn : 0 < N := (Nat.two_pow_pos _).trans_le hsize
  have hnq : (0 : ℚ) < N := by exact_mod_cast hn
  have hc : 320 * ((p : ℚ) + 1) ^ 2 / t ^ 2 ≤ (C : ℚ) := Nat.le_ceil _
  have hnat := LogarithmicBudget.log_square_lt C 1 N hsize
  have hq : (C : ℚ) * ((N.log2 : ℚ) + 1) ^ 2 < N := by exact_mod_cast hnat
  have hsmall : 320 * ((p : ℚ) + 1) ^ 2 * ((N.log2 : ℚ) + 1) ^ 2 < (N : ℚ) * t ^ 2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos ht)).mp
    calc
      _ = (320 * ((p : ℚ) + 1) ^ 2 / t ^ 2) * ((N.log2 : ℚ) + 1) ^ 2 := by ring
      _ ≤ (C : ℚ) * ((N.log2 : ℚ) + 1) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ < _ := hq
  by_contra! hle
  have hd : (d : ℚ) ≤ ((p : ℚ) + 1) * ((N.log2 : ℚ) + 1) := by exact_mod_cast hle
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg d) (by positivity)).2 hd
  have hln : (N.log2 : ℚ) ≤ N := by exact_mod_cast Nat.log2_le_self N
  have hfalse : (t * N) ^ 2 < (t * N) ^ 2 := calc
    _ ≤ 320 * (N.log2 : ℚ) * (d : ℚ) ^ 2 := hsquare
    _ ≤ (320 * (N : ℚ)) * (((p : ℚ) + 1) * ((N.log2 : ℚ) + 1)) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hln (by norm_num)) hsq (sq_nonneg _) (by positivity)
    _ = (N : ℚ) * (320 * ((p : ℚ) + 1) ^ 2 * ((N.log2 : ℚ) + 1) ^ 2) := by ring
    _ < (N : ℚ) * (N * t ^ 2) := mul_lt_mul_of_pos_left hsmall hnq
    _ = _ := by ring
  exact (lt_irrefl _) hfalse

/-- Each polynomial power is strictly smaller than 2^d past its cutoff. -/
theorem polynomial_lt_pow (t : ℚ) (N d p : ℕ) (ht : 0 < t)
    (hsquare : (t * N) ^ 2 ≤ 320 * (N.log2 : ℚ) * (d : ℚ) ^ 2)
    (hsize : threshold t p ≤ N) : N ^ p < 2 ^ d := by
  have hbig := exponent_exceeds_log t N d p ht hsquare hsize
  have hpow : (N.log2 + 1) * p < d := calc
    _ = p * (N.log2 + 1) := Nat.mul_comm _ _
    _ ≤ (p + 1) * (N.log2 + 1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    _ < d := hbig
  calc
    N ^ p ≤ (2 ^ (N.log2 + 1)) ^ p := Nat.pow_le_pow_left Nat.lt_log2_self.le _
    _ = 2 ^ ((N.log2 + 1) * p) := (pow_mul _ _ _).symm
    _ < 2 ^ d := Nat.pow_lt_pow_right (by decide : 1 < 2) hpow

/-- An application may provide the exponent existentially with its verified
lower bound on total cost. -/
theorem polynomial_lt_cost (t : ℚ) (N cost p : ℕ) (ht : 0 < t)
    (hsize : threshold t p ≤ N)
    (hcost : ∃ d : ℕ, (t * N) ^ 2 ≤ 320 * (N.log2 : ℚ) * (d : ℚ) ^ 2 ∧ 2 ^ d ≤ cost) :
    N ^ p < cost := by
  obtain ⟨d, hd, hw⟩ := hcost
  exact (polynomial_lt_pow t N d p ht hd hsize).trans_le hw

#print axioms exponent_exceeds_log
#print axioms polynomial_lt_pow
#print axioms polynomial_lt_cost

end PowerCost
