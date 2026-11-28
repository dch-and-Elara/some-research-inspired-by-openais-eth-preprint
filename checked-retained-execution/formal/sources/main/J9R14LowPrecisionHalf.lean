import J6R9PacketLocal
import PrecisionErasure

/-!
# Real Appendix D coefficients in the residual variable 2z

The residue-variable change is integral: the printed signed grid has
v2(t-q) <= a, so 2^a/(t-q) already has odd denominator. Taking half of
the original slope therefore does not invert two in the receiving ring.
An unmatched same-packet Cauchy entry has *zero* constant coefficient.
-/

namespace J9R14LowPrecisionHalf
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P1DyadicGrid J6R9PacketCoeff

noncomputable section

theorem halfSlope_twoLocal {a : ℕ} {t q : ℤ} (ht : t∈grid a)
    (hq : q∈grid a) (hne : t≠q) :
    ((2:ℚ)^a / ((t:ℚ)-(q:ℚ))) ∈ twoLocalSubalgebra := by
  have hd := sub_ne_zero.mpr hne
  obtain ⟨w,how,he⟩ := integer_odd_factor hd
  have hv := grid_difference_valuation_le ht hq hne
  have hn : ¬ (2:ℤ) ∣ w := fun h => (Int.not_even_iff_odd.mpr how) (even_iff_two_dvd.mpr h)
  apply (mem_twoLocal_iff _).mpr
  refine ⟨(2:ℤ)^(a-padicValInt 2 (t-q)),w,hn,?_⟩
  have hdq : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast hd
  have hwq : (w:ℚ) ≠ 0 := by exact_mod_cast odd_int_ne_zero how
  apply (div_eq_div_iff hdq hwq).mpr
  have hq' : (t:ℚ)-(q:ℚ) = (2:ℚ)^(padicValInt 2 (t-q))*(w:ℚ) := by
    change t-q = _ at he
    unfold pow₂ at he
    exact_mod_cast he
  rw [hq',Int.cast_pow,Int.cast_ofNat,← mul_assoc,← pow_add,Nat.sub_add_cancel hv]

def halfSlope (a : ℕ) (t q : ℤ) : TwoLocal :=
  if h : t∈grid a ∧ q∈grid a ∧ t≠q then
    ⟨(2:ℚ)^a/((t:ℚ)-(q:ℚ)),halfSlope_twoLocal h.1 h.2.1 h.2.2⟩
  else 0

theorem slope_twice (a : ℕ) (t q : ℤ) :
    J6ActiveLocalFactor.slope a t q = 2 * halfSlope a t q := by
  by_cases h : t∈grid a ∧ q∈grid a ∧ t≠q
  · rw [J6ActiveLocalFactor.slope,dif_pos h,halfSlope,dif_pos h]
    apply Subtype.ext
    change (2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ)) = 2*((2:ℚ)^a/((t:ℚ)-(q:ℚ)))
    rw [pow_succ,div_eq_mul_inv,div_eq_mul_inv]
    ring
  · simp [J6ActiveLocalFactor.slope,halfSlope,h]

def factorsHalf (a : ℕ) (t : ℤ) (s : Finset ℤ) : TwoLocal[X] :=
  ∏ q ∈ s, (1+C (halfSlope a t q)*X)

def cHatHalf (a : ℕ) (t : ℤ) : TwoLocal[X] :=
  C (rho a t)*factorsHalf a t ((grid a).erase t)

def wHalf (a : ℕ) (t k : ℤ) : TwoLocal[X] :=
  if k=t then cHatHalf a t else
    C (rho a t)*C (halfSlope a t k)*X*factorsHalf a t (((grid a).erase t).erase k)

theorem factors_eval_half {R : Type*} [CommRing R] (ψ : TwoLocal→+*R)
    (a : ℕ) (t : ℤ) (s : Finset ℤ) (z : R) :
    (factorsHalf a t s).eval₂ ψ (2*z) = (J6R9PacketLocal.factors a t s).eval₂ ψ z := by
  have htwo : (2:TwoLocal[X]).eval₂ ψ z=(2:R) :=
    map_ofNat (Polynomial.eval₂RingHom ψ z) 2
  rw [factorsHalf,J6R9PacketLocal.factors,Polynomial.eval₂_finset_prod,Polynomial.eval₂_finset_prod]
  apply Finset.prod_congr rfl
  intro q _
  simp only [Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_mul,
    Polynomial.eval₂_C,Polynomial.eval₂_X,slope_twice,map_mul,map_ofNat,htwo]
  ring

theorem cHat_eval_half {R : Type*} [CommRing R] (ψ : TwoLocal→+*R) (a : ℕ) (t : ℤ) (z : R) :
    (cHatHalf a t).eval₂ ψ (2*z) = (cHat a t).eval₂ ψ z := by
  unfold cHatHalf cHat
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,factors_eval_half]
  rfl

theorem w_eval_half {R : Type*} [CommRing R] (ψ : TwoLocal→+*R)
    (a : ℕ) (t k : ℤ) (z : R) :
    (wHalf a t k).eval₂ ψ (2*z) = (J6R9PacketLocal.W a t k).eval₂ ψ z := by
  have htwo : (2:TwoLocal[X]).eval₂ ψ z=(2:R) :=
    map_ofNat (Polynomial.eval₂RingHom ψ z) 2
  by_cases h : k=t
  · simp only [wHalf,J6R9PacketLocal.W,if_pos h,cHat_eval_half]
  · simp only [wHalf,J6R9PacketLocal.W,if_neg h,Polynomial.eval₂_mul,Polynomial.eval₂_C,
      Polynomial.eval₂_X,slope_twice,map_mul,map_ofNat,factors_eval_half,htwo]
    ring

theorem w_constant (a : ℕ) (t k : ℤ) :
    (wHalf a t k).coeff 0 = if k=t then rho a t else 0 := by
  by_cases h : k=t
  · simp [wHalf,h,cHatHalf,factorsHalf,Polynomial.mul_coeff_zero,Polynomial.coeff_zero_prod]
  · simp [wHalf,h,Polynomial.mul_coeff_zero]

#print axioms halfSlope_twoLocal
#print axioms slope_twice
#print axioms w_eval_half
#print axioms w_constant

end
end J9R14LowPrecisionHalf
