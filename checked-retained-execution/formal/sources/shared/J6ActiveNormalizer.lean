import J6ActiveUniqueness
import J6ActiveSchedule
import DenominatorBudget
import Mathlib.Algebra.Ring.GeomSum

/-! Normalized Appendix D Hermite factors in the two-local ring. No
even denominator is inverted in the receiving ring. The compatible
quotient polynomial is computed by polynomial arithmetic and a monic
truncation, so reduction commutes with forming that quotient. -/
namespace J6ActiveNormalizer
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid

theorem slope_twoLocal {a : ℕ} {t q : ℤ} (ht : t ∈ grid a)
    (hq : q ∈ grid a) (hne : t ≠ q) :
    ((2:ℚ)^(a+1) / ((t:ℚ)-(q:ℚ))) ∈ twoLocalSubalgebra := by
  have hd := sub_ne_zero.mpr hne
  obtain ⟨w,how,he⟩ := integer_odd_factor hd
  have hv := grid_difference_valuation_le ht hq hne
  have hn : ¬ (2:ℤ) ∣ w := fun h => (Int.not_even_iff_odd.mpr how) (even_iff_two_dvd.mpr h)
  apply (mem_twoLocal_iff _).mpr
  refine ⟨(2:ℤ)^(a+1-padicValInt 2 (t-q)),w,hn,?_⟩
  have hdq : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast hd
  have hwq : (w:ℚ) ≠ 0 := by exact_mod_cast odd_int_ne_zero how
  apply (div_eq_div_iff hdq hwq).mpr
  have hq' : (t:ℚ)-(q:ℚ) = (2:ℚ)^(padicValInt 2 (t-q))*(w:ℚ) := by
    change t-q = _ at he
    unfold pow₂ at he
    exact_mod_cast he
  rw [hq', Int.cast_pow, Int.cast_ofNat, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel (hv.trans (Nat.le_succ _))]

/-- This is the polynomial used to implement division by the normalized
local factor modulo X^k for factors with constant term 1. -/
noncomputable def quotientJet {A : Type*} [CommRing A] (k : ℕ) (E F : A[X]) : A[X] :=
  (F * ∑ j ∈ Finset.range k, (1-E)^j) %ₘ X^k

theorem quotientJet_map {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (k : ℕ) (E F : A[X]) :
    (quotientJet k E F).map ψ = quotientJet k (E.map ψ) (F.map ψ) := by
  unfold quotientJet
  rw [Polynomial.map_modByMonic ψ (monic_X.pow k), Polynomial.map_pow, Polynomial.map_X]
  simp only [Polynomial.map_mul, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one]

#print axioms slope_twoLocal
#print axioms quotientJet_map
end J6ActiveNormalizer