import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

/-! Exact scaled Hermite data over commutative rings, allowing nilpotents.
The Appendix D recovery uses the characteristic-zero coefficient algebra,
where images of nonzero rational scalars are units. This result is not
an assertion of unit separation after reduction modulo (2^p). -/
namespace J6ActiveUniqueness
open scoped BigOperators Polynomial
open Polynomial

variable {R I : Type*} [CommRing R]

noncomputable def coord (a : Rˣ) (t : R) : R[X] := C (a : R) * X + C t

noncomputable def back (a : Rˣ) (t : R) : R[X] := C (↑a⁻¹ : R) * (X - C t)

noncomputable def atNode (a : Rˣ) (t : R) : R[X] →+* R[X] := Polynomial.compRingHom (coord a t)

theorem atNode_apply (a : Rˣ) (t : R) (f : R[X]) :
    atNode a t f = f.comp (coord a t) := rfl

theorem back_comp (a : Rˣ) (t : R) : (back a t).comp (coord a t) = X := by
  simp only [back, coord, mul_comp, C_comp, sub_comp, X_comp, add_sub_cancel_right,
    ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem coord_comp (a : Rˣ) (t : R) : (coord a t).comp (back a t) = X := by
  simp only [back, coord, add_comp, mul_comp, X_comp, C_comp, ← mul_assoc,
    ← map_mul, Units.mul_inv, map_one, one_mul, sub_add_cancel]

theorem atNode_degree (a : Rˣ) (t : R) (f : R[X]) :
    (atNode a t f).natDegree ≤ f.natDegree := by
  have hc : (coord a t).natDegree ≤ 1 := by
    unfold coord
    have hd : (C (a:R) * X).natDegree ≤ 1 :=
      le_trans natDegree_mul_le (by simpa using (natDegree_X_le (R := R)))
    exact le_trans (natDegree_add_le _ _) (by simpa using hd)
  apply le_trans natDegree_comp_le
  simpa using Nat.mul_le_mul_left f.natDegree hc

theorem back_degree (a : Rˣ) (t : R) (f : R[X]) :
    (f.comp (back a t)).natDegree ≤ f.natDegree := by
  have hc : (back a t).natDegree ≤ 1 := by
    unfold back
    exact natDegree_mul_le.trans (by simpa using natDegree_X_sub_C_le t)
  apply le_trans natDegree_comp_le
  simpa using Nat.mul_le_mul_left f.natDegree hc

/-- Divisibility of the original polynomial by the centre factor is
equivalent to vanishing of the scaled local coefficients to the same order. -/
theorem factor_dvd_iff (a : Rˣ) (t : R) (f : R[X]) (k : ℕ) :
    (X - C t)^k ∣ f ↔ (X : R[X])^k ∣ atNode a t f := by
  letI : Invertible (a : R) := ⟨(↑a⁻¹ : R), by simp, by simp⟩
  rw [atNode_apply, coord, dvd_comp_C_mul_X_add_C_iff, pow_comp, X_comp]
  change (X - C t)^k ∣ f ↔ (C (↑a⁻¹ : R) * (X - C t))^k ∣ f
  rw [mul_pow, ((isUnit_C.mpr (a⁻¹).isUnit).pow k).mul_left_dvd]

theorem factor_dvd_sub_iff (a : Rˣ) (t : R) (k : ℕ) (f g : R[X]) :
    (X - C t)^k ∣ (f-g) ↔
    ∀ j < k, (atNode a t f).coeff j = (atNode a t g).coeff j := by
  rw [factor_dvd_iff a, X_pow_dvd_iff, map_sub]
  simp only [coeff_sub, sub_eq_zero]

/-- All centres and orders are explicit; zero orders cause no problem.
The product divisor is monic even in coefficient rings with zero divisors. -/
theorem jets_determine (s : Finset I) (node : I → R) (k : I → ℕ) (a : Rˣ)
    (separated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsUnit (node i - node j))
    (f g : R[X]) (hf : f.natDegree < ∑ i ∈ s, k i)
    (hg : g.natDegree < ∑ i ∈ s, k i)
    (hjets : ∀ i ∈ s, ∀ j < k i,
      (atNode a (node i) f).coeff j = (atNode a (node i) g).coeff j) : f = g := by
  classical
  nontriviality R
  let D : I → R[X] := fun i => (X - C (node i))^k i
  have hmon (i : I) : (D i).Monic := (monic_X_sub_C _).pow _
  have hn : (∏ i ∈ s, D i).natDegree = ∑ i ∈ s, k i := by
    rw [natDegree_prod_of_monic s D (fun i _ => hmon i)]
    simp only [D, Monic.natDegree_pow (monic_X_sub_C _), natDegree_X_sub_C, mul_one]
  have hd : (∏ i ∈ s, D i) ∣ (f-g) := by
    apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact (isCoprime_X_sub_C_of_isUnit_sub (separated i hi j hj hij)).pow
    · intro i hi
      exact (factor_dvd_sub_iff a (node i) (k i) f g).mpr (hjets i hi)
  apply sub_eq_zero.mp
  by_contra h0
  apply (monic_prod_of_monic _ _ (fun i _ => hmon i)).not_dvd_of_natDegree_lt h0 _ hd
  rw [hn]
  exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hf hg)

/-- Distinct integer centres become unit-separated over any rational algebra,
including the nilpotent double coefficient extension of Appendix D. -/
theorem integer_centres_units [Algebra ℚ R] (i j : ℤ) (h : i ≠ j) :
    IsUnit ((i : R) - (j : R)) := by
  have hn : (i : ℚ) - (j : ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
  simpa using (isUnit_iff_ne_zero.mpr hn).map (algebraMap ℚ R)

#print axioms back_comp
#print axioms coord_comp
#print axioms atNode_degree
#print axioms back_degree
#print axioms factor_dvd_iff
#print axioms factor_dvd_sub_iff
#print axioms jets_determine
#print axioms integer_centres_units
end J6ActiveUniqueness