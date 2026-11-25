import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators Polynomial
open Polynomial

namespace Reconstruction.ReleaseColor.AffineInterpolation

noncomputable section

variable {q : ℕ} {F : Type*} [Field F]

/-- The nodal polynomial, and its quotient by a single node factor. -/
def nodePolynomial (a : Fin q → F) : F[X] := ∏ t, (X - C (a t))
def nodeQuotient (a : Fin q → F) (t : Fin q) : F[X] :=
  ∏ s ∈ Finset.univ.erase t, (X - C (a s))
def nodeDenominator (a : Fin q → F) (t : Fin q) : F :=
  (nodeQuotient a t).eval (a t)

private theorem node_factor (a : Fin q → F) (t : Fin q) :
    nodePolynomial a = (X - C (a t)) * nodeQuotient a t := by
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)).symm

theorem derivative_at_node (a : Fin q → F) (t : Fin q) :
    (derivative (nodePolynomial a)).eval (a t) = nodeDenominator a t := by
  rw [node_factor a t, derivative_mul]
  simp [nodeDenominator]

theorem denominator_ne_zero (a : Fin q → F) (hi : Function.Injective a) (t : Fin q) :
    nodeDenominator a t ≠ 0 := by
  rw [nodeDenominator, nodeQuotient, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro s hs
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr fun he => (Finset.mem_erase.mp hs).1 ((hi he).symm)

private theorem quotient_eval_other (a : Fin q → F) {s t : Fin q} (h : s ≠ t) :
    (nodeQuotient a t).eval (a s) = 0 := by
  rw [nodeQuotient, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ s⟩) (by simp)

private theorem quotient_degree (a : Fin q → F) (t : Fin q) :
    (nodeQuotient a t).natDegree = q-1 := by
  rw [nodeQuotient, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp [natDegree_X_sub_C, Finset.card_erase_of_mem (Finset.mem_univ t)]

private theorem quotient_coeff (a : Fin q → F) (t : Fin q) :
    (nodeQuotient a t).coeff (q-1) = 1 := by
  rw [← quotient_degree a t, coeff_natDegree]
  exact (monic_prod_X_sub_C a (Finset.univ.erase t)).leadingCoeff

/-- Interpolation on the given nodes with values b. -/
def interpolate (a b : Fin q → F) : F[X] :=
  ∑ t, C (b t / nodeDenominator a t) * nodeQuotient a t

theorem interpolate_eval (a b : Fin q → F) (hi : Function.Injective a) (t : Fin q) :
    (interpolate a b).eval (a t) = b t := by
  simp only [interpolate, eval_finset_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single t]
  · change b t / nodeDenominator a t * nodeDenominator a t = b t
    exact div_mul_cancel₀ _ (denominator_ne_zero a hi t)
  · intro s _ hs
    rw [quotient_eval_other a hs.symm, mul_zero]
  · simp

theorem interpolate_degree (a b : Fin q → F) : (interpolate a b).natDegree ≤ q-1 := by
  unfold interpolate
  apply natDegree_sum_le_of_forall_le
  intro t _
  exact (natDegree_C_mul_le ..).trans (quotient_degree a t).le

private theorem interpolate_reproduces (a : Fin q → F) (hi : Function.Injective a)
    (f : F[X]) (hf : f.natDegree < q) :
    interpolate a (fun t => f.eval (a t)) = f := by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hi
  · intro t
    rw [eval_sub, interpolate_eval _ _ hi, sub_self]
  · rw [Fintype.card_fin]
    exact (natDegree_sub_le ..).trans_lt
      (max_lt (lt_of_le_of_lt (interpolate_degree a _) (by omega)) hf)

theorem leading_coefficient_formula (a : Fin q → F) (hi : Function.Injective a)
    (f : F[X]) (hf : f.natDegree < q) :
    f.coeff (q-1) = ∑ t, f.eval (a t) / (derivative (nodePolynomial a)).eval (a t) := by
  have h := congrArg (fun p : F[X] => p.coeff (q-1)) (interpolate_reproduces a hi f hf)
  simpa [interpolate, derivative_at_node, finset_sum_coeff, coeff_C_mul, quotient_coeff]
    using h.symm

/-- The particular scaled interpolation vector from Lemma 4. -/
def scaledInterpolate (a z : Fin q → F) : F[X] :=
  interpolate a (fun t => a t * nodeDenominator a t * z t)

theorem scaled_at_zero (a z : Fin q → F) (hi : Function.Injective a) :
    (scaledInterpolate a z).eval 0 = -(nodePolynomial a).eval 0 * ∑ t, z t := by
  simp only [scaledInterpolate, interpolate, eval_finset_sum, eval_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have he : (nodePolynomial a).eval 0 = -(a t) * (nodeQuotient a t).eval 0 := by
    rw [node_factor a t, eval_mul]
    simp
  rw [he]
  have hden := denominator_ne_zero a hi t
  field_simp [hden] <;> ring

theorem scaled_at_node (a z : Fin q → F) (hi : Function.Injective a) (t : Fin q) :
    (scaledInterpolate a z).eval (a t) =
      a t * (derivative (nodePolynomial a)).eval (a t) * z t := by
  rw [scaledInterpolate, interpolate_eval _ _ hi, derivative_at_node]

theorem nodePolynomial_zero_ne (a : Fin q → F) (hn : ∀ t, a t ≠ 0) :
    (nodePolynomial a).eval 0 ≠ 0 := by
  rw [nodePolynomial, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  simp [hn t]

private theorem scaled_moment (a z : Fin q → F) (hi : Function.Injective a) (j : ℕ)
    (hd : ((X^j : F[X]) * scaledInterpolate a z).natDegree < q) :
    ((X^j : F[X]) * scaledInterpolate a z).coeff (q-1) =
      ∑ t, (a t)^(j+1) * z t := by
  rw [leading_coefficient_formula a hi _ hd]
  apply Finset.sum_congr rfl
  intro t _
  rw [eval_mul, eval_X_pow, scaled_at_node a z hi, derivative_at_node, pow_succ]
  field_simp [denominator_ne_zero a hi t] <;> ring

/-- The q-2 vanishing moments of Lemma 4 are equivalent to the interpolated
polynomial being affine. This includes the empty moment list at q=2. -/
theorem scaled_affine_iff_moments (a z : Fin q → F) (hi : Function.Injective a)
    (hq : 2 ≤ q) :
    (scaledInterpolate a z).natDegree ≤ 1 ↔
      ∀ j ∈ Finset.range (q-2), ∑ t, (a t)^(j+1) * z t = 0 := by
  constructor
  · intro ha j hj
    have hj' := Finset.mem_range.mp hj
    have hd : ((X^j : F[X]) * scaledInterpolate a z).natDegree < q-1 := by
      have hm := natDegree_mul_le (p := (X^j : F[X])) (q := scaledInterpolate a z)
      rw [natDegree_X_pow] at hm
      omega
    exact (scaled_moment a z hi j (hd.trans_le (Nat.sub_le _ _))).symm.trans
      (coeff_eq_zero_of_natDegree_lt hd)
  · intro hz
    by_contra! hd
    let f := scaledInterpolate a z
    let j := q-1-f.natDegree
    have hf : f.natDegree ≤ q-1 := interpolate_degree _ _
    have hf0 : f ≠ 0 := by intro he; simp [f, he] at hd
    have hj : j ∈ Finset.range (q-2) := by
      rw [Finset.mem_range]
      change 1 < f.natDegree at hd
      dsimp [j]
      omega
    have hd' : ((X^j : F[X]) * f).natDegree = q-1 := by
      rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hf0, natDegree_X_pow]
      dsimp [j]
      omega
    have hn : ((X^j : F[X]) * f) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hf0
    have hcoeff : ((X^j : F[X]) * f).coeff (q-1) ≠ 0 := by
      rw [← hd', coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hn
    apply hcoeff
    rw [scaled_moment a z hi j (by change ((X^j : F[X]) * f).natDegree < q; omega)]
    exact hz j hj


/-- Dividing the scaled nodal value recovers its original vector coordinate. -/
theorem scaled_samples_recover (a z : Fin q → F) (hi : Function.Injective a)
    (hn : ∀ t, a t ≠ 0) (t : Fin q) :
    (scaledInterpolate a z).eval (a t) /
        (a t * (derivative (nodePolynomial a)).eval (a t)) = z t := by
  rw [scaled_at_node a z hi, derivative_at_node, mul_comm _ (z t),
    mul_div_cancel_right₀ _ (mul_ne_zero (hn t) (denominator_ne_zero a hi t))]

/-- Interpolating each physical coordinate preserves the common measurement kernel. -/
theorem scaled_common_kernel {V M : Type*} [Fintype V] (a : Fin q → F)
    (hi : Function.Injective a) (hq : 0 < q) (C : M → V → F) (z : Fin q → V → F)
    (hz : ∀ t j, ∑ v, C j v * z t v = 0) (j : M) :
    ∑ v, Polynomial.C (C j v) * scaledInterpolate a (fun t => z t v) = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hi
  · intro t
    simp only [eval_finset_sum, eval_mul, eval_C, scaled_at_node _ _ hi]
    have he : (∑ v, C j v * (a t * (derivative (nodePolynomial a)).eval (a t) * z t v)) =
        (a t * (derivative (nodePolynomial a)).eval (a t)) * ∑ v, C j v * z t v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    rw [he,hz t j,mul_zero]
  · rw [Fintype.card_fin]
    apply lt_of_le_of_lt _ (show q-1 < q by omega)
    apply natDegree_sum_le_of_forall_le
    intro v _
    exact (natDegree_C_mul_le ..).trans (interpolate_degree _ _)

end
end Reconstruction.ReleaseColor.AffineInterpolation
