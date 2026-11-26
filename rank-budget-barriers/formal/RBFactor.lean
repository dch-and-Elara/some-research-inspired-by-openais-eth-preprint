import RBDeterminant
/-! Inner-factor budgets proved by a polynomial block determinant identity. -/
namespace RankBudget
open Matrix Polynomial
open scoped BigOperators

/-- Determinantal divisibility for a low-inner-rank perturbation of a multiple
of q. No choice of bases or normal-form theorem is needed. -/
theorem factorThrough_dvd {S n r : Type*} [CommRing S] [IsDomain S]
    [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]
    (q : S) (hq : q ≠ 0) (E : Matrix n n S) (A : Matrix n r S) (B : Matrix r n S) :
    q ^ (Fintype.card n - Fintype.card r) ∣ (q • E + A * B).det := by
  classical
  by_cases h : Fintype.card r ≤ Fintype.card n
  · let H := Matrix.fromBlocks E A (-B) (q • (1 : Matrix r r S))
    let T := Matrix.fromBlocks (q • (1 : Matrix n n S)) (0 : Matrix n r S) B (1 : Matrix r r S)
    have hblock : H * T = Matrix.fromBlocks (q • E + A * B) A (0 : Matrix r n S)
        (q • (1 : Matrix r r S)) := by
      simp [H, T, Matrix.fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul]
    have ht : T.det = q ^ Fintype.card n := by
      simp [T, Matrix.det_fromBlocks_zero₁₂]
    have heq := congrArg Matrix.det hblock
    rw [Matrix.det_mul, ht, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
        mul_one] at heq
    have ht' : q ^ Fintype.card n =
        q ^ (Fintype.card n - Fintype.card r) * q ^ Fintype.card r := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [ht', ← mul_assoc] at heq
    have hf := mul_right_cancel₀ (pow_ne_zero (Fintype.card r) hq) heq
    exact ⟨H.det, by rw [← hf, mul_comm]⟩
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)]

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Each truncated node may use a different inner factor size and different
jets. Representatives A,B need not be constant or degree-bounded. -/
theorem innerRankBudget (P : Matrix n n K[X]) (d : ℕ) (s : Finset K) (k r : K → ℕ)
    (pne : P.det ≠ 0) (degBound : ∀ i j, (P i j).natDegree ≤ d)
    (fit : ∀ t ∈ s, ∃ (E : Matrix n n K[X]) (A : Matrix n (Fin (r t)) K[X])
      (B : Matrix (Fin (r t)) n K[X]), P = (X - C t) ^ k t • E + A * B) :
    (∑ t ∈ s, k t * (Fintype.card n - r t)) ≤ Fintype.card n * d := by
  refine (multiplicityBudget P.det pne s _ ?_).trans (detDegree_le _ _ degBound)
  intro t ht
  obtain ⟨E,A,B,h⟩ := fit t ht
  rw [h, pow_mul]
  simpa using factorThrough_dvd ((X - C t) ^ k t)
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero t)) E A B

end RankBudget