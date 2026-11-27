import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.GaussLemma

open Polynomial
open scoped BigOperators

namespace GrenetRankAlgebra

variable {D F K : Type*} [CommRing D] [CommRing F] [Field K]

/-- A bounded reciprocal with constant coefficient 1 is monic of the stated degree. -/
theorem reflect_monic_degree (p : D[X]) (d : ℕ) [Nontrivial D]
    (hdeg : p.natDegree ≤ d) (h0 : p.coeff 0 = 1) :
    (p.reflect d).Monic ∧ (p.reflect d).natDegree = d := by
  have hc : (p.reflect d).coeff d = 1 := by
    rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, h0]
  have hle : (p.reflect d).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_reflect, revAt, Function.Embedding.coeFn_mk, if_neg (not_le.mpr hi)]
    exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hi)
  have heq : (p.reflect d).natDegree = d :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, heq, hc], heq⟩

/-- The reciprocal of a normalized residual polynomial reduces to a pure power. -/
theorem reflect_reduce (red : D →+* F) (q : D[X]) (d : ℕ)
    (hq : q.map red = 1) : (q.reflect d).map red = X ^ d := by
  rw [← reflect_map, hq, reflect_one]

/-- Translating the reciprocal by one gives the other half-block's residue. -/
theorem reflect_shift_reduce (red : D →+* F) (q : D[X]) (d : ℕ)
    (hq : q.map red = 1) : ((q.reflect d).comp (X + 1)).map red = (X + 1) ^ d := by
  rw [Polynomial.map_comp, reflect_reduce red q d hq]
  simp

/-- Coprimality after reduction lifts for monic polynomials over an integrally closed
domain, via the monic common divisor in the fraction field. -/
theorem isCoprime_fraction_map_of_monic_reduction [Nontrivial F] [IsDomain D] [IsIntegrallyClosed D]
    [Algebra D K] [IsFractionRing D K] (red : D →+* F)
    {p q : D[X]} (hp : p.Monic) (hq : q.Monic)
    (hc : IsCoprime (p.map red) (q.map red)) :
    IsCoprime (p.map (algebraMap D K)) (q.map (algebraMap D K)) := by
  classical
  let a := p.map (algebraMap D K)
  let b := q.map (algebraMap D K)
  let g := EuclideanDomain.gcd a b
  have hgL : g ∣ a := EuclideanDomain.gcd_dvd_left a b
  have hgR : g ∣ b := EuclideanDomain.gcd_dvd_right a b
  have hgn : g ≠ 0 := ne_zero_of_dvd_ne_zero ((hp.map _).ne_zero) hgL
  obtain ⟨G, hG⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp hgL
  have hGn : G.Monic := by
    apply ((IsFractionRing.injective D K).monic_map_iff).mpr
    have hEq : G.map (algebraMap D K) = g * C g.leadingCoeff⁻¹ := by
      calc
        G.map (algebraMap D K) =
            (G.map (algebraMap D K) * C g.leadingCoeff) * C g.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hgn),
            map_one, mul_one]
        _ = _ := congrArg (fun p : K[X] => p * C g.leadingCoeff⁻¹) hG
    rw [hEq]
    exact monic_mul_leadingCoeff_inv hgn
  have hdL : G ∣ p :=
    Monic.dvd_of_fraction_map_dvd_fraction_map hp hGn
      (dvd_trans ⟨_, hG.symm⟩ hgL)
  have hdR : G ∣ q :=
    Monic.dvd_of_fraction_map_dvd_fraction_map hq hGn
      (dvd_trans ⟨_, hG.symm⟩ hgR)
  have hU : IsUnit (G.map red) :=
    hc.isUnit_of_dvd' (map_dvd (Polynomial.mapRingHom red) hdL)
      (map_dvd (Polynomial.mapRingHom red) hdR)
  have hOne : G = 1 := by
    apply hGn.natDegree_eq_zero_iff_eq_one.mp
    rw [← hGn.natDegree_map red, (hGn.map red).eq_one_of_isUnit hU, natDegree_one]
  rw [hOne, Polynomial.map_one, one_mul] at hG
  apply EuclideanDomain.gcd_isUnit_iff.mp
  change IsUnit g
  rw [← hG]
  exact isUnit_C.mpr (leadingCoeff_ne_zero.mpr hgn).isUnit

/-- The reciprocal residual and its translate are coprime over the fraction field. -/
theorem isCoprime_reflect_shift [Nontrivial F] [IsDomain D] [IsIntegrallyClosed D]
    [Algebra D K] [IsFractionRing D K] (red : D →+* F)
    (q : D[X]) (d : ℕ) (hdeg : q.natDegree ≤ d) (h0 : q.coeff 0 = 1)
    (hred : q.map red = 1) :
    IsCoprime ((q.reflect d).map (algebraMap D K))
      (((q.reflect d).comp (X + 1)).map (algebraMap D K)) := by
  have hM := (reflect_monic_degree q d hdeg h0).1
  apply isCoprime_fraction_map_of_monic_reduction red hM
    (q := (q.reflect d).comp (X + 1))
    (hM.comp (by simpa using monic_X_add_C (1 : D))
      (by rw [← C_1, natDegree_X_add_C]; exact one_ne_zero))
  rw [reflect_reduce red q d hred, reflect_shift_reduce red q d hred]
  apply IsCoprime.pow
  exact ⟨-1, 1, by ring⟩

section Factors

variable {ι : Type*}

/-- Reflecting a power of a linear factor also works when the linear term is zero. -/
theorem reflect_linear_pow (a : D) (m : ℕ) :
    (reflect m ((1 + C a * X) ^ m) = (X + C a) ^ m) ∧
    (((1 + C a * X) ^ m).natDegree ≤ m) := by
  have hlin : (1 + C a * X : D[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le (n := 1)
    · simp
    · exact (natDegree_mul_le ..).trans (by rw [natDegree_C, zero_add]; exact natDegree_X_le)
  have hr : reflect 1 (1 + C a * X) = X + C a := by
    rw [reflect_add, reflect_one, reflect_C_mul, reflect_one_X, mul_one, pow_one]
  induction m with
  | zero => simp [reflect_one]
  | succ m ih =>
    constructor
    · rw [pow_succ, reflect_mul _ _ ih.2 hlin, ih.1, hr, pow_succ]
    · rw [pow_succ]
      exact (natDegree_mul_le ..).trans (Nat.add_le_add ih.2 hlin)

/-- Reflect a product with the total number of linear factors as its degree bound. -/
theorem reflect_linear_product (s : Finset ι) (a : ι → D) (m : ι → ℕ) :
    let P := ∏ i ∈ s, (1 + C (a i) * X) ^ m i
    let n := ∑ i ∈ s, m i
    P.natDegree ≤ n ∧ reflect n P = ∏ i ∈ s, (X + C (a i)) ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have h := reflect_linear_pow (a i) (m i)
    exact ⟨(natDegree_mul_le ..).trans (Nat.add_le_add h.2 ih.1),
      by rw [reflect_mul _ _ h.2 ih.1, h.1, ih.2]⟩

end Factors

end GrenetRankAlgebra
