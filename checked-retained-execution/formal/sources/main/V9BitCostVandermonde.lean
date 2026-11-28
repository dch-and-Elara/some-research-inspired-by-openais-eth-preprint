import V9BitCostInterpolation
import Mathlib.Tactic

/-!
# Denominator-free tile inversion from J7 scaled integer moments

J7 already supplies integral moments around a public nonzero integer
scale. After subtracting the public nonpin contributions at that same
scale, inversion needs only integer coefficients and one exact division
per pin. This module verifies the readout and all prefix-width bounds.
-/

open scoped BigOperators Polynomial

namespace V9BitCostVandermonde

open Polynomial V9BitCostInterpolation

theorem multiplyLinear_coeff (P : ℤ[X]) (y : ℤ) (k : ℕ) :
    (P*(X-C y)).coeff k =
      (if 0 < k then P.coeff (k-1) else 0) - P.coeff k*y := by
  cases k with
  | zero => simp [mul_sub]
  | succ k => simp [mul_sub]

/-- Bounds every partial product, not just the final Vandermonde numerator. -/
theorem factor_coeff_abs_le (ys : List ℤ) (B : ℤ) (hB : 0 ≤ B)
    (hy : ∀ y ∈ ys, |y| ≤ B) :
    ∀ k, |(productFactors ys).coeff k| ≤ (B+1)^ys.length := by
  induction ys with
  | nil =>
    intro k
    simp only [productFactors, List.length_nil, pow_zero, Polynomial.coeff_one]
    split <;> norm_num
  | cons y ys ih =>
    intro k
    have hy0 := hy y (List.mem_cons_self)
    have ih' := ih (fun z hz => hy z (List.mem_cons_of_mem _ hz))
    let bound := (B+1)^ys.length
    have hb : 0 ≤ bound := by dsimp [bound]; positivity
    have hfirst : |if 0 < k then (productFactors ys).coeff (k-1) else 0| ≤ bound := by
      split
      · exact ih' _
      · simpa using hb
    have hsecond : |(productFactors ys).coeff k*y| ≤ bound*B := by
      rw [abs_mul]
      exact mul_le_mul (ih' k) hy0 (abs_nonneg _) hb
    rw [productFactors, multiplyLinear_coeff]
    calc
      _ ≤ |if 0 < k then (productFactors ys).coeff (k-1) else 0| +
          |(productFactors ys).coeff k*y| := by
        simpa using abs_sub_le (if 0 < k then (productFactors ys).coeff (k-1) else 0)
          (0:ℤ) ((productFactors ys).coeff k*y)
      _ ≤ bound+bound*B := add_le_add hfirst hsecond
      _ = _ := by simp only [bound, List.length_cons, pow_succ]; ring

theorem tile_coeff_abs_le {d : ℕ} (x : Fin (d+1) → ℤ) (i : Fin (d+1)) (B : ℤ)
    (hB : 0 ≤ B) (hx : ∀ j, |x j| ≤ B) (k : ℕ) :
    |(numerator x i).coeff k| ≤ (B+1)^d := by
  rw [← productFactors_other]
  have hx' : ∀ y ∈ other x i, |y| ≤ B := by
    intro y hy
    unfold other at hy
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hx j
  simpa only [other_length] using factor_coeff_abs_le (other x i) B hB hx' k

/-- The scaled J7 moment, after nonpin contributions have been subtracted. -/
def moment {d : ℕ} (x score : Fin (d+1) → ℤ) (k : Fin (d+1)) : ℤ :=
  ∑ j, (x j)^k.val * score j

noncomputable def integerReadout {d : ℕ}
    (x observed : Fin (d+1) → ℤ) (i : Fin (d+1)) : ℤ :=
  ∑ k, (numerator x i).coeff k.val * observed k

/-- A coefficient vector is the transpose Vandermonde inverse up to
its one readily computable, possibly even integer denominator. -/
theorem integerReadout_factor {d : ℕ} (x score : Fin (d+1) → ℤ) (i : Fin (d+1)) :
    integerReadout x (moment x score) i = (numerator x i).eval (x i)*score i := by
  let P := numerator x i
  have hP : P.natDegree < d+1 := Nat.lt_succ_of_le (numerator_degree x i)
  have hEval (z : ℤ) : P.eval z = ∑ k : Fin (d+1), P.coeff k.val*z^k.val := by
    have he := congrArg (Polynomial.eval z) (Polynomial.as_sum_range' P (d+1) hP)
    simpa only [Polynomial.eval_finset_sum, Polynomial.eval_monomial,
      ← Fin.sum_univ_eq_sum_range] using he
  simp only [integerReadout, moment, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · change ∑ k : Fin (d+1), P.coeff k.val*(x i^k.val*score i) = P.eval (x i)*score i
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← hEval]
  · intro j _ hj
    change ∑ k : Fin (d+1), P.coeff k.val*(x j^k.val*score j) = 0
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← hEval]
    rw [numerator_off_diagonal x hj, zero_mul]

theorem denominator_ne_zero {d : ℕ} (x : Fin (d+1) → ℤ) (hx : Function.Injective x)
    (i : Fin (d+1)) : (numerator x i).eval (x i) ≠ 0 := by
  rw [numerator, Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => by
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) ((hx h).symm)))

/-- Solving a tile needs no rational intermediate once the source data
and the public nonpin subtractions have been scaled by the same integer.
If the requested score was Z_g times a bit, one further exact division
by Z_g recovers that bit. -/
theorem integerReadout_div_exact {d : ℕ} (x score : Fin (d+1) → ℤ)
    (hx : Function.Injective x) (i : Fin (d+1)) :
    integerReadout x (moment x score) i / (numerator x i).eval (x i) = score i := by
  rw [integerReadout_factor, mul_comm]
  exact Int.mul_ediv_cancel (score i) (denominator_ne_zero x hx i)

/-- The actual J7 normalization uses a public integer scale Zg. One can
subtract the nonpin contributions at that same scale and recover a pin
without a rational Gaussian-elimination intermediate. -/
theorem recover_scaled_pin {d : ℕ}
    (x pins raw correction : Fin (d+1) → ℤ) (scale : ℤ) (hs : scale ≠ 0)
    (hx : Function.Injective x)
    (hData : ∀ k, raw k-correction k = scale*moment x pins k)
    (i : Fin (d+1)) :
    (integerReadout x (fun k => raw k-correction k) i / (numerator x i).eval (x i)) /
      scale = pins i := by
  have he : (fun k => raw k-correction k) = moment x (fun j => scale*pins j) := by
    funext k
    rw [hData k, moment, moment, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [he, integerReadout_div_exact _ _ hx, mul_comm scale (pins i)]
  exact Int.mul_ediv_cancel (pins i) hs

/-- The denominator is a product of at most d integer differences of
length at most L; no oddness assumption is needed on it. -/
theorem denominator_abs_le {d : ℕ} (x : Fin (d+1) → ℤ) (i : Fin (d+1))
    (L : ℤ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ L) :
    |(numerator x i).eval (x i)| ≤ L^d := by
  rw [numerator, Polynomial.eval_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin (d+1))).erase i, L := by
      refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact abs_le.mpr ⟨by linarith [(hx j).2, (hx i).1], by linarith [(hx i).2, (hx j).1]⟩
    _ = _ := by simp

/-- Dot-product work at one pin. The bound applies to every prefix
or other subset of accumulated terms in a usual exact integer loop. -/
theorem dot_partial_abs_le {d : ℕ} (x observed : Fin (d+1) → ℤ)
    (i : Fin (d+1)) (B M : ℤ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hx : ∀ j, |x j| ≤ B) (hm : ∀ k, |observed k| ≤ M) (s : Finset (Fin (d+1))) :
    |∑ k ∈ s, (numerator x i).coeff k.val*observed k| ≤ (d+1:ℤ)*(B+1)^d*M := by
  calc
    _ ≤ ∑ k ∈ s, |(numerator x i).coeff k.val*observed k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ s, (B+1)^d*M := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (tile_coeff_abs_le x i B hB hx _) (hm k) (abs_nonneg _) (by positivity)
    _ = (s.card:ℤ)*((B+1)^d*M) := by simp
    _ ≤ _ := by
      have hcard : (s.card:ℤ) ≤ (d+1:ℤ) := by
        exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin (d+1))
      calc
        _ ≤ (d+1:ℤ)*((B+1)^d*M) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

#print axioms factor_coeff_abs_le
#print axioms integerReadout_factor
#print axioms integerReadout_div_exact
#print axioms recover_scaled_pin
#print axioms denominator_abs_le
#print axioms dot_partial_abs_le

end V9BitCostVandermonde

