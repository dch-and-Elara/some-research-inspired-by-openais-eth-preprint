import J6R14SpecializedBoxNativeTransport
import J6ActiveNormalizer

/-! Re-express the actual cancelled packet weights as polynomials in
Y = 2*zeta over the same odd localization, with no division by two
in the receiving ring. This is a constructive choice of the honest
higher row tails; the identity holds at every finite probe. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators
open Polynomial DenominatorBudget P1DyadicGrid J6R9PacketCoeff J6R9PacketLocal

private theorem half_slope_integral {a : ℕ} {t q : ℤ}
    (ht : t∈grid a) (hq : q∈grid a) (hne : t≠q) :
    ((2:ℚ)^a / ((t:ℚ)-(q:ℚ))) ∈ twoLocalSubalgebra := by
  have hd := sub_ne_zero.mpr hne
  obtain ⟨w,how,he⟩ := integer_odd_factor hd
  have hv := grid_difference_valuation_le ht hq hne
  have hn : ¬(2:ℤ) ∣ w := fun h => (Int.not_even_iff_odd.mpr how) (even_iff_two_dvd.mpr h)
  refine (mem_twoLocal_iff _).mpr ⟨(2:ℤ)^(a-padicValInt 2 (t-q)),w,hn,?_⟩
  have hdq : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast hd
  have hwq : (w:ℚ) ≠ 0 := by exact_mod_cast odd_int_ne_zero how
  apply (div_eq_div_iff hdq hwq).mpr
  have hq' : (t:ℚ)-(q:ℚ) = (2:ℚ)^(padicValInt 2 (t-q))*(w:ℚ) := by
    unfold pow₂ at he
    exact_mod_cast he
  rw [hq',Int.cast_pow,Int.cast_ofNat,← mul_assoc,← pow_add,Nat.sub_add_cancel hv]

noncomputable def halfSlope (a : ℕ) (t q : ℤ) : TwoLocal :=
  if h : t∈grid a ∧ q∈grid a ∧ t≠q then
    ⟨(2:ℚ)^a/((t:ℚ)-(q:ℚ)), half_slope_integral h.1 h.2.1 h.2.2⟩ else 0

theorem halfSlope_double (a : ℕ) (t q : ℤ) :
    2 * halfSlope a t q = J6ActiveLocalFactor.slope a t q := by
  unfold halfSlope J6ActiveLocalFactor.slope
  split_ifs with h
  · apply twoLocalRat_injective
    rw [map_mul,map_ofNat]
    change 2*((2:ℚ)^a/((t:ℚ)-(q:ℚ))) = (2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ))
    rw [pow_succ',mul_div_assoc]
  · rw [mul_zero]

noncomputable def halfFactors (a : ℕ) (t : ℤ) (s : Finset ℤ) : TwoLocal[X] :=
  ∏ q ∈ s, (1 + C (halfSlope a t q)*X)

noncomputable def cHatHalf (a : ℕ) (t : ℤ) : TwoLocal[X] :=
  C (rho a t) * halfFactors a t ((grid a).erase t)

noncomputable def WHalf (a : ℕ) (t k : ℤ) : TwoLocal[X] :=
  if k=t then cHatHalf a t else
    C (rho a t)*C (halfSlope a t k)*X*halfFactors a t (((grid a).erase t).erase k)

section Receive
variable {A : Type*} [CommRing A]

theorem halfFactors_eval_twice (a : ℕ) (t : ℤ) (s : Finset ℤ)
    (ψ : TwoLocal →+* A) (z : A) :
    (halfFactors a t s).eval₂ ψ (2*z) = (factors a t s).eval₂ ψ z := by
  let E₂ := Polynomial.eval₂RingHom ψ (2*z)
  let E := Polynomial.eval₂RingHom ψ z
  change E₂ (halfFactors a t s) = E (factors a t s)
  unfold halfFactors factors
  rw [map_prod,map_prod]
  refine Finset.prod_congr rfl ?_
  intro q _
  change (1+C (halfSlope a t q)*X).eval₂ ψ (2*z) =
    (1+C (J6ActiveLocalFactor.slope a t q)*X).eval₂ ψ z
  have hs := congrArg ψ (halfSlope_double a t q)
  rw [map_mul,map_ofNat] at hs
  simp only [eval₂_add,eval₂_mul,eval₂_one,eval₂_C,eval₂_X,← hs]
  ring

theorem cHatHalf_eval_twice (a : ℕ) (t : ℤ) (ψ : TwoLocal→+* A) (z : A) :
    (cHatHalf a t).eval₂ ψ (2*z) = (cHat a t).eval₂ ψ z := by
  change (C (rho a t)*halfFactors a t ((grid a).erase t)).eval₂ ψ (2*z) =
    (C (rho a t)*factors a t ((grid a).erase t)).eval₂ ψ z
  simp only [eval₂_mul,eval₂_C,halfFactors_eval_twice]

theorem WHalf_eval_twice (a : ℕ) (t k : ℤ) (ψ : TwoLocal→+* A) (z : A) :
    (WHalf a t k).eval₂ ψ (2*z) = (W a t k).eval₂ ψ z := by
  by_cases hk : k=t
  · simp only [WHalf,W,if_pos hk,cHatHalf_eval_twice]
  · have hs := congrArg ψ (halfSlope_double a t k)
    rw [map_mul,map_ofNat] at hs
    simp only [WHalf,W,if_neg hk,eval₂_mul,eval₂_C,eval₂_X,halfFactors_eval_twice,← hs]
    ring
end Receive

theorem WHalf_coeff0 (a : ℕ) (t k : ℤ) : (WHalf a t k).coeff 0 = (W a t k).coeff 0 := by
  simpa only [mul_zero,eval₂_at_zero,map_id] using
    WHalf_eval_twice a t k (RingHom.id TwoLocal) 0

#print axioms halfSlope
#print axioms halfSlope_double
#print axioms halfFactors_eval_twice
#print axioms cHatHalf_eval_twice
#print axioms WHalf_eval_twice
#print axioms WHalf_coeff0
end J6R14SpecializedBox
