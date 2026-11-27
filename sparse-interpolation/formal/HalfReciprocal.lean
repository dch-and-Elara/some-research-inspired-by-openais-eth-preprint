import GrenetPaper
import StrictDenominator

open Polynomial Matrix SharpDifference GrenetResidue
open scoped BigOperators

namespace GrenetPaper

/-- The actual even-row polynomial matrix in the start Z. -/
noncomputable def evenPolynomialMatrix {k : ℕ} (E : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) ℚ[X] :=
  Matrix.of fun i j => (X + C (2*(i.val : ℚ)))^(E j)

theorem reflect_source_det {k : ℕ} (E : Fin k → ℕ) :
    ((sourceMatrix E).det).reflect (∑ j, E j) = (evenPolynomialMatrix E).det := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine ((Set.finite_singleton (0 : ℚ)).infinite_compl).mono ?_
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  change eval x ((sourceMatrix E).det.reflect (∑ j, E j)) =
    eval x (evenPolynomialMatrix E).det
  let ev (y : ℚ) := Polynomial.evalRingHom y
  have hm : (ev x⁻¹).mapMatrix (sourceMatrix E) =
      (ev x).mapMatrix (evenPolynomialMatrix E) *
        diagonal (fun j => (x⁻¹)^(E j)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    change ev x⁻¹ ((1 + (i.val : ℚ[X])*twoU)^(E j)) =
      ev x ((X + C (2*(i.val : ℚ)))^(E j)) * (x⁻¹)^(E j)
    simp only [map_pow, map_add, map_one, map_mul, map_natCast, ev, twoU,
      coe_evalRingHom, eval_X, eval_C, eval_ofNat]
    rw [← mul_pow]
    congr 1
    rw [add_mul, mul_inv_cancel₀ hx0]
    ring
  have hh : eval x⁻¹ (sourceMatrix E).det =
      eval x (evenPolynomialMatrix E).det * (x⁻¹)^(∑ j, E j) := by
    change ev x⁻¹ (sourceMatrix E).det = ev x (evenPolynomialMatrix E).det * _
    rw [RingHom.map_det, hm, Matrix.det_mul, Matrix.det_diagonal,
      ← RingHom.map_det, Finset.prod_pow_eq_pow_sum]
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
  have hr := eval₂_reflect_mul_pow (RingHom.id ℚ) x⁻¹ _
    (sourceMatrix E).det (natDegree_source_det_le E)
  rw [invOf_eq_inv, inv_inv, eval₂_id, eval₂_id, hh] at hr
  exact mul_right_cancel₀ (pow_ne_zero _ (inv_ne_zero hx0)) hr

private theorem budget_ge_odd {h : ℕ} (E : Fin (2*h) → ℕ)
    (he : Function.Injective E) (A : LocalPoly)
    (hA : normalized E = oddFactors h E * A) :
    (2*h).choose 2 + (deficit h E)^2 ≤ ∑ j, E j := by
  have hAne : A ≠ 0 := by
    intro hz
    have hh := (GrenetRankArendt.normalized_residual_budget h E he A hA).1
    rw [hz, coeff_zero] at hh
    exact zero_ne_one hh
  have hodd : oddFactors h E ≠ 0 := (oddFactors_unit_leadingCoeff h E).ne_zero ∘
    leadingCoeff_eq_zero.mpr
  have hd := natDegree_lift_normalized_bound E he
  change (2*h).choose 2 + ((normalized E).map toRat).natDegree ≤ ∑ j, E j at hd
  rw [natDegree_map_eq_of_injective Subtype.val_injective,
    hA, natDegree_mul hodd hAne, GrenetRankArendt.natDegree_oddFactors] at hd
  omega

private theorem exponentV_constant {k : ℕ} (E : Fin k → ℕ) :
    exponentV E = C ((Matrix.vandermonde (fun j => (E j : ℚ))).det) := by
  unfold exponentV
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.vandermonde, liftPoly]

/-- The polynomial reciprocal factorization from Section 4 includes Z=0.
The factor on the left is the unnormalized determinant. -/
theorem evenPolynomialMatrix_factor {h : ℕ} (E : Fin (2*h) → ℕ)
    (he : Function.Injective E) (A : LocalPoly)
    (hA : normalized E = oddFactors h E * A) :
    let K := (2*h).choose 2
    let d := (∑ j, E j) - K - (deficit h E)^2
    (evenPolynomialMatrix E).det =
      C (2^K * (Matrix.vandermonde (fun j => (E j : ℚ))).det) *
      ((∏ j ∈ Finset.range (2*h),
          (X + C (((2*j+1 : ℕ) : ℚ))) ^ GrenetResidue.multiplicity E (2*j+1)) *
        (A.reflect d).map toRat) := by
  let K := (2*h).choose 2
  let S := ∑ j, E j
  let M := (deficit h E)^2
  let d := S - K - M
  let v := (Matrix.vandermonde (fun j => (E j : ℚ))).det
  have hS : S = K + (M+d) := by
    dsimp [S, K, M, d]
    have := budget_ge_odd E he A hA
    omega
  have hd : A.natDegree ≤ d :=
    (GrenetRankArendt.normalized_residual_budget h E he A hA).2
  have hM : (oddFactors h E).natDegree = M := GrenetRankArendt.natDegree_oddFactors h E
  have hbound : (liftPoly (oddFactors h E * A)).natDegree ≤ M+d :=
    natDegree_map_le.trans (natDegree_mul_le.trans (Nat.add_le_add hM.le hd))
  have hh : (sourceMatrix E).det = C (2^K*v) * (X^K * liftPoly (oddFactors h E * A)) := by
    rw [normalized_factorization, hA, exponentV_constant, twoU, mul_pow]
    change ((2 : ℚ[X])^K * X^K) * C v * _ = _
    have htwo : (2 : ℚ[X]) = C (2 : ℚ) := (C_eq_natCast (R := ℚ) 2).symm
    have hp : (2 : ℚ[X])^K = C ((2 : ℚ)^K) := by
      rw [htwo, map_pow]
    rw [hp, map_mul (C : ℚ →+* ℚ[X])]
    ac_rfl
  have ho : (oddFactors h E).reflect M =
      ∏ j ∈ Finset.range (2*h), (X + C (((2*j+1 : ℕ) : D))) ^
        GrenetResidue.multiplicity E (2*j+1) := by
    have hsum := sum_center_multiplicities h E 1 (by decide)
    change (∑ j ∈ Finset.range (2*h), GrenetResidue.multiplicity E (2*j+1)) = M at hsum
    rw [← hsum]
    exact (GrenetRankAlgebra.reflect_linear_product (Finset.range (2*h))
      (fun j => ((2*j+1 : ℕ) : D)) (fun j => GrenetResidue.multiplicity E (2*j+1))).2
  change (evenPolynomialMatrix E).det = C (2^K*v) * (_ * (A.reflect d).map toRat)
  rw [← reflect_source_det, hh, show (∑ j, E j) = K+(M+d) from hS, reflect_C_mul,
    reflect_mul _ _ (natDegree_X_pow_le K) hbound, reflect_monomial, revAt_le le_rfl,
    Nat.sub_self, pow_zero, one_mul]
  change C (2^K*v) * (((oddFactors h E * A).map toRat).reflect (M+d)) = _
  rw [reflect_map toRat (oddFactors h E * A) (M+d), reflect_mul _ _ hM.le hd,
    Polynomial.map_mul, ho, Polynomial.map_prod]
  apply congrArg (fun P : ℚ[X] => C (2^K*v) * (P * (A.reflect d).map toRat))
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X]
  change (X + (Polynomial.mapRingHom toRat) ((2*j+1 : ℕ) : D[X]))^_ = _
  rw [map_natCast, C_eq_natCast]


private theorem residue_nontrivial : Nontrivial ModTwo := by
  apply Ideal.Quotient.nontrivial
  intro h
  have hm : (1 : D) ∈ Ideal.span ({(2 : D)} : Set D) := by rw [h]; trivial
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  have hrat : (1 : ℚ) = 2 * toRat a := by simpa using congrArg toRat ha
  have he : toRat a = 1 / 2 := by linarith
  have hd : (1 / 2 : ℚ) ∈ localTwo := he ▸ a.property
  have hv := (mem_localTwo_iff_val _).mp hd
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  rw [one_div, padicValRat.inv, htwo] at hv
  omega

/-- Simultaneous zeros of the even and odd half-blocks can only occur
at one of the explicit shifted odd-center factors. -/
theorem even_and_odd_common_root {K : Type*} [Field K] (q : ℚ →+* K)
    {h : ℕ} (E : Fin (2*h) → ℕ) (he : Function.Injective E) (z : K)
    (hz : (evenPolynomialMatrix E).det.eval₂ q z = 0)
    (hz1 : (evenPolynomialMatrix E).det.eval₂ q (z+1) = 0) :
    ∃ j ∈ Finset.range (2*h), GrenetResidue.multiplicity E (2*j+1) ≠ 0 ∧
      (z = -((2*j+1 : ℕ) : K) ∨ z+1 = -((2*j+1 : ℕ) : K)) := by
  classical
  obtain ⟨A, hA, hr⟩ := normalized_odd_part h E he
  obtain ⟨ha0, hdeg⟩ := GrenetRankArendt.normalized_residual_budget h E he A hA
  let d := (∑ j, E j) - (2*h).choose 2 - (deficit h E)^2
  have hfac := evenPolynomialMatrix_factor E he A hA
  dsimp only at hfac
  let C0 : ℚ := 2 ^ (2*h).choose 2 * (Matrix.vandermonde (fun j => (E j : ℚ))).det
  let s := Finset.range (2*h)
  let P : ℚ[X] := ∏ j ∈ s, (X+C (((2*j+1 : ℕ) : ℚ))) ^ GrenetResidue.multiplicity E (2*j+1)
  let G : ℚ[X] := (A.reflect d).map toRat
  change (evenPolynomialMatrix E).det = C C0 * (P*G) at hfac
  have hC : q C0 ≠ 0 := by
    apply (map_ne_zero_iff q q.injective).mpr
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Matrix.det_vandermonde_ne_zero_iff.mpr
      (fun i j hh => he (Nat.cast_injective (R := ℚ) hh)))
  by_contra hn
  have gzero (y : K) (hSide : y = z ∨ y = z+1)
      (hy : (evenPolynomialMatrix E).det.eval₂ q y = 0) : G.eval₂ q y = 0 := by
    rw [hfac, eval₂_mul, eval₂_C, eval₂_mul] at hy
    have hp : P.eval₂ q y ≠ 0 := by
      intro hp
      change (eval₂RingHom q y) P = 0 at hp
      unfold P at hp
      rw [map_prod] at hp
      obtain ⟨j, hj, hroot⟩ := Finset.prod_eq_zero_iff.mp hp
      rw [map_pow] at hroot
      have hm : GrenetResidue.multiplicity E (2*j+1) ≠ 0 :=
        fun hm => by rw [hm, pow_zero] at hroot; exact one_ne_zero hroot
      have hval : (eval₂RingHom q y) (X+C (((2*j+1 : ℕ) : ℚ))) = 0 := by
        by_contra hv
        exact (pow_ne_zero _ hv) hroot
      change eval₂ q y (X+C (((2*j+1 : ℕ) : ℚ))) = 0 at hval
      rw [eval₂_add, eval₂_X, eval₂_C, map_natCast] at hval
      have hY := eq_neg_of_add_eq_zero_left hval
      exact hn ⟨j, hj, hm, hSide.elim (fun h => Or.inl (h.symm.trans hY))
        (fun h => Or.inr (h.symm.trans hY))⟩
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hC)).resolve_left hp
  have h0 := gzero z (Or.inl rfl) hz
  have h1 := gzero (z+1) (Or.inr rfl) hz1
  letI : Nontrivial ModTwo := residue_nontrivial
  letI : IsIntegrallyClosed D :=
    (Valuation.valuationSubring.integers (Rat.padicValuation 2)).isIntegrallyClosed
  have hc := GrenetRankAlgebra.isCoprime_reflect_shift (K := ℚ) modTwo A d hdeg ha0 hr
  obtain ⟨u, v, huv⟩ := hc
  have h1' : (((A.reflect d).comp (X+1)).map (algebraMap D ℚ)).eval₂ q z = 0 := by
    rw [Polynomial.map_comp]
    simpa [G, eval₂_comp, toRat] using h1
  have H := congrArg (eval₂RingHom q z) huv
  simp only [map_add, map_mul, map_one] at H
  change _ * G.eval₂ q z + _ * (((A.reflect d).comp (X+1)).map (algebraMap D ℚ)).eval₂ q z = 1 at H
  rw [h0, h1', mul_zero, mul_zero, add_zero] at H
  exact zero_ne_one H

private theorem residue_equiv_of_prime {D' F : Type*} [CommRing D'] [CommRing F]
    [Nontrivial F] (p : ℕ) [Fact p.Prime] (emb : D' →+* ℚ)
    (he : Function.Injective emb) (red : D' →+* F) (hs : Function.Surjective red)
    (hp0 : (p : F) = 0) (hden : ∀ x : D', ¬p ∣ (emb x).den) :
    Nonempty (F ≃+* ZMod p) := by
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero (R := F) Fact.out).mpr hp0
  let r : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  refine ⟨(RingEquiv.ofBijective r ⟨r.injective, ?_⟩).symm⟩
  intro y
  obtain ⟨x, rfl⟩ := hs y
  let a := emb x
  have hdQ : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hd : (a.den : ZMod p) ≠ 0 := fun h => hden x ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hx : x*(a.den : D') = (a.num : D') := by
    apply he
    rw [map_mul, map_natCast, map_intCast]
    change a * (a.den : ℚ) = a.num
    exact (div_eq_iff hdQ).mp a.num_div_den |>.symm
  have hx' : red x * (a.den : F) = (a.num : F) := by
    simpa only [map_mul, map_intCast, map_natCast] using congrArg red hx
  refine ⟨(a.num : ZMod p)/(a.den : ZMod p), ?_⟩
  have hu : IsUnit ((a.den : F)) := by
    simpa only [map_natCast] using ((isUnit_iff_ne_zero.mpr hd).map r)
  apply sub_eq_zero.mp
  apply hu.mul_left_eq_zero.mp
  rw [sub_mul, hx']
  have hd' := congrArg r (div_mul_cancel₀ (a.num : ZMod p) hd)
  exact sub_eq_zero.mpr (by simpa only [map_mul, map_natCast, map_intCast] using hd')

theorem strict_localization_denominator (p : ℕ) [Fact p.Prime] (z : ℚ) :
    z ∈ GrenetStrict.localP p ↔ ¬ p ∣ z.den := by
  rw [GrenetStrict.mem_localP_iff]
  constructor
  · intro hn hp
    have hz := GrenetStrict.inverse_val_of_dvd_den p z hp
    rw [padicValRat.inv] at hz
    have hpos := one_le_padicValNat_of_dvd (p := p) z.den_ne_zero hp
    have hpos' : (1 : ℤ) ≤ padicValNat p z.den := by exact_mod_cast hpos
    omega
  · intro hp
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hp, Nat.cast_zero, sub_zero]
    exact Int.natCast_nonneg _

/-- The actual rational valuation subring in the strict proof has
the stated residue field F_p. -/
theorem strict_residue_field (p : ℕ) [Fact p.Prime] :
    Nonempty (IsLocalRing.ResidueField (GrenetStrict.D p) ≃+* ZMod p) := by
  let r := GrenetStrict.residue p
  have hp : p.Prime := Fact.out
  have hzero : (p : IsLocalRing.ResidueField (GrenetStrict.D p)) = 0 := by
    rw [← map_natCast r]
    apply GrenetStrict.residue_zero_of_pos
    rw [map_natCast, padicValRat.self hp.one_lt]
    decide
  refine residue_equiv_of_prime p (GrenetStrict.toRat p) Subtype.val_injective r
    IsLocalRing.residue_surjective hzero ?_
  intro x
  exact (strict_localization_denominator p (GrenetStrict.toRat p x)).mp x.property

/-- The mod-two quotient used in the parity proof is precisely F_2. -/
theorem parity_residue_field : Nonempty (ModTwo ≃+* ZMod 2) := by
  letI : Nontrivial ModTwo := residue_nontrivial
  have hzero : (2 : ModTwo) = 0 := by simpa using modTwo_two
  refine residue_equiv_of_prime 2 toRat Subtype.val_injective modTwo
    Ideal.Quotient.mk_surjective hzero ?_
  intro x hx
  have ho := (mem_localTwo_iff_odd_den _).mp x.property
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hx)
end GrenetPaper
