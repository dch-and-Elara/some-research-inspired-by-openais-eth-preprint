import J6ActiveNormalizer
import J6ActiveHermite

/-! A normalized local factor on the actual printed grid is an explicit
finite polynomial over the two-local integers. The whole normalizer is
a product of these factors, so the reciprocal jet can be computed over
the integral ring and reduced without inverting an even denominator. -/
namespace J6ActiveLocalFactor
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid J6ActiveUniqueness J6ActiveHermite

noncomputable def alpha (a : ℕ) : ℚˣ :=
  Units.mk0 ((2:ℚ)^(a+1)) (pow_ne_zero _ (by decide))

noncomputable def slope (a : ℕ) (t q : ℤ) : TwoLocal :=
  if h : t ∈ grid a ∧ q ∈ grid a ∧ t ≠ q then
    ⟨((2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ))), J6ActiveNormalizer.slope_twoLocal h.1 h.2.1 h.2.2⟩
  else 0

theorem integral_factor {a : ℕ} {t q : ℤ}
    (ht : t ∈ grid a) (hq : q ∈ grid a) (hne : t ≠ q) :
    (1 + C (slope a t q) * X).map twoLocalRat =
      atNode (alpha a) (t:ℚ) (C (((t:ℚ)-(q:ℚ))⁻¹) * (X-C (q:ℚ))) := by
  have hs : twoLocalRat (slope a t q) = (2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ)) := by
    rw [slope, dif_pos ⟨ht,hq,hne⟩]
    rfl
  have hα : (alpha a : ℚ) = (2:ℚ)^(a+1) := rfl
  have hd : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  simp only [Polynomial.map_add,Polynomial.map_one,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,hs,atNode_apply,coord,mul_comp,sub_comp,X_comp,C_comp,hα]
  rw [show C ((2:ℚ)^(a+1))*X + C (t:ℚ) - C (q:ℚ) =
    C ((2:ℚ)^(a+1))*X + C ((t:ℚ) - (q:ℚ)) by rw [map_sub]; ring]
  rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hd, map_one, add_comm]
  rw [div_eq_mul_inv, mul_comm ((2:ℚ)^(a+1)) _]

noncomputable def integralNormalizer (a : ℕ) (s : Finset ℤ) (k : ℤ → ℕ) (t : ℤ) :
    TwoLocal[X] :=
  ∏ q ∈ s.erase t, (1 + C (slope a t q) * X)^k q

theorem integralNormalizer_spec {a : ℕ} {t : ℤ} (s : Finset ℤ) (k : ℤ→ℕ)
    (ht : t ∈ grid a) (hs : s ⊆ grid a) :
    (integralNormalizer a s k t).map twoLocalRat =
      atNode (alpha a) (t:ℚ)
        (normalizer s (fun q : ℤ => (q:ℚ)) k (fun t q => ((t:ℚ)-(q:ℚ))⁻¹) t) := by
  unfold integralNormalizer normalizer
  simp only [Polynomial.map_prod,Polynomial.map_pow,map_prod,map_pow]
  apply Finset.prod_congr rfl
  intro q hq
  rw [integral_factor ht (hs (Finset.mem_erase.mp hq).2) (Finset.mem_erase.mp hq).1.symm]

#print axioms integral_factor
#print axioms integralNormalizer_spec
end J6ActiveLocalFactor