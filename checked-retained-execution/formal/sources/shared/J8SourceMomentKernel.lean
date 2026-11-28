import J8SourceMoment

/-!
Literal Cauchy and geometric-target first jets for J8. The source
polynomial is a product on the actual grid, and target division is
tested by the finite certificate modulo the square of the probe variable.
The statement is rational and independent of the receiving probe ring.
-/

namespace J8SourceMoment

open scoped BigOperators Polynomial
open Polynomial

noncomputable section

def cauchyTranslated (grid : Finset ℚ) (t alpha : ℚ) : ℚ[X] :=
  ∏ q ∈ grid, (C (t-q) + C alpha * X)

def cauchyDenominator (grid : Finset ℚ) : ℚ :=
  ∏ q ∈ grid.erase 0, -q

/-- Ratio C'(t)/C'(0) expressed by its literal products. -/
def centerRatio (grid : Finset ℚ) (t : ℚ) : ℚ :=
  (∏ q ∈ grid.erase t, (t-q)) / cauchyDenominator grid

theorem denominator_nonzero (grid : Finset ℚ) : cauchyDenominator grid ≠ 0 := by
  unfold cauchyDenominator
  exact Finset.prod_ne_zero_iff.mpr
    (fun q h => neg_ne_zero.mpr ((Finset.mem_erase.mp h).1))

theorem cauchyTranslated_split (grid : Finset ℚ) (t alpha : ℚ) (ht : t ∈ grid) :
    cauchyTranslated grid t alpha =
      (C alpha * X) * ∏ q ∈ grid.erase t, (C (t-q) + C alpha * X) := by
  unfold cauchyTranslated
  rw [← Finset.mul_prod_erase _ _ ht]
  simp

/-- First jet of the translated numerator (with the printed 2^b
factor for the coordinate-zero target tile). -/
def crossingNumerator (grid : Finset ℚ) (t alpha : ℚ) (b : ℕ) : ℚ[X] :=
  C ((2:ℚ)^b / cauchyDenominator grid) * cauchyTranslated grid t alpha

theorem numerator_jet (grid : Finset ℚ) (t alpha : ℚ) (b : ℕ) (ht : t ∈ grid) :
    (crossingNumerator grid t alpha b).coeff 0 = 0 ∧
    (crossingNumerator grid t alpha b).coeff 1 = centerRatio grid t * alpha * 2^b := by
  classical
  have zeroP : (C alpha * (X : ℚ[X])).coeff 0 = 0 := by
    simp [Polynomial.mul_coeff_zero]
  have oneP : (C alpha * (X : ℚ[X])).coeff 1 = alpha := by
    simp [Polynomial.mul_coeff_one]
  have h0 : (cauchyTranslated grid t alpha).coeff 0 = 0 := by
    rw [cauchyTranslated_split grid t alpha ht, Polynomial.mul_coeff_zero, zeroP, zero_mul]
  have h1 : (cauchyTranslated grid t alpha).coeff 1 =
      alpha * ∏ q ∈ grid.erase t, (t-q) := by
    rw [cauchyTranslated_split grid t alpha ht,
      TargetDerivative.first_mul_vanishing_target _ _ zeroP, oneP,
      Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp
  constructor
  · simp [crossingNumerator, Polynomial.mul_coeff_zero, h0]
  · rw [crossingNumerator, Polynomial.mul_coeff_one, h0, h1]
    simp only [Polynomial.coeff_C_zero, mul_zero, add_zero, centerRatio, div_eq_mul_inv]
    ring

def crossingDenPoly (denom alpha : ℚ) (b : ℕ) : ℚ[X] :=
  (C denom + C alpha * X)^(b+1)

/-- For an honest first-order quotient, no names or assumptions about its
actual Taylor coefficients are needed. The remainder is a multiple of
the probe variable squared, precisely the first-jet congruence. -/
theorem crossing_quotient_jet (grid : Finset ℚ) (t alpha denom : ℚ) (b : ℕ)
    (ht : t ∈ grid) (hd : denom ≠ 0) (k error : ℚ[X])
    (quotient : k * crossingDenPoly denom alpha b =
      crossingNumerator grid t alpha b + X^2 * error) :
    k.coeff 0 = 0 ∧ k.coeff 1 = exactSlope (centerRatio grid t) alpha denom b := by
  have hden : (crossingDenPoly denom alpha b).coeff 0 = denom^(b+1) := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp [crossingDenPoly]
  have den_ne : denom^(b+1) ≠ 0 := pow_ne_zero _ hd
  have h := numerator_jet grid t alpha b ht
  have e0 : ((X : ℚ[X])^2 * error).coeff 0 = 0 := by
    simp [pow_two, Polynomial.mul_coeff_zero]
  have e1 : ((X : ℚ[X])^2 * error).coeff 1 = 0 := by
    simp [pow_two, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one]
  have q0 := congrArg (fun p : ℚ[X] => p.coeff 0) quotient
  simp only [Polynomial.mul_coeff_zero, hden, Polynomial.coeff_add, h.1, e0, add_zero] at q0
  have k0 : k.coeff 0 = 0 := (mul_eq_zero.mp q0).resolve_right den_ne
  refine ⟨k0, ?_⟩
  have q1 := congrArg (fun p : ℚ[X] => p.coeff 1) quotient
  simp only [Polynomial.mul_coeff_one, hden, k0, zero_mul, zero_add, Polynomial.coeff_add,
    h.2, e1, add_zero] at q1
  simpa [exactSlope] using (eq_div_iff den_ne).mpr q1

/-- The printed unnormalization of one mode at retained coordinate zero. -/
def rescaleOuter (a b : ℕ) (normalized : ℚ[X]) : ℚ[X] :=
  C ((2:ℚ)^(a+1+b)) * (X * normalized.comp (C 2 * X))

theorem rescale_first (a b : ℕ) (normalized : ℚ[X]) :
    (rescaleOuter a b normalized).coeff 1 =
      2^(a+1+b) * normalized.coeff 0 := by
  have h0 : (normalized.comp (C 2 * (X : ℚ[X]))).coeff 0 = normalized.coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_eq_eval_zero normalized]
    simp
  simp only [rescaleOuter, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    h0, zero_mul, mul_zero, one_mul, zero_add, add_zero]

/-- The actual normalized target constant equals the Cauchy ratio over
the positive odd denominator power. This is the scalar needed to match
the normalized first-coefficient register, with no modulo-two inversion
of any Vandermonde determinant. -/
theorem normalized_target_constant (grid : Finset ℚ) (t denom : ℚ) (a b : ℕ)
    (ht : t ∈ grid) (hd : denom ≠ 0) (f error : ℚ[X])
    (quotient : rescaleOuter a b f * crossingDenPoly denom (2^(a+1)) b =
      crossingNumerator grid t (2^(a+1)) b + X^2 * error) :
    f.coeff 0 = centerRatio grid t / denom^(b+1) := by
  have h := (crossing_quotient_jet grid t (2^(a+1)) denom b ht hd _ error quotient).2
  rw [rescale_first, exactSlope] at h
  apply mul_left_cancel₀ (pow_ne_zero (a+1+b) (by norm_num : (2:ℚ) ≠ 0))
  rw [h, pow_add]
  ring

/-- At the actual extreme node a legal crossing denominator is positive
and odd: equal parity at the row and tile, and even packet length. -/
theorem outer_crossing_denom (L tau x : ℕ) (hL : 2 < L) (he : Even L)
    (hτ : tau < 2) (parity : x % 2 = tau) :
    0 < (L:ℤ) - 1 - tau + x ∧ Odd ((L:ℤ) - 1 - tau + x) := by
  refine ⟨by omega, ?_⟩
  obtain ⟨h,hh⟩ := he
  refine ⟨(h:ℤ) + (x / 2 : ℕ) - 1, ?_⟩
  omega

#print axioms numerator_jet
#print axioms crossing_quotient_jet
#print axioms normalized_target_constant
#print axioms outer_crossing_denom

end
end J8SourceMoment
