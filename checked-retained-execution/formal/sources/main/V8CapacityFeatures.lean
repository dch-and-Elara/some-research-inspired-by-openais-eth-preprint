import V8CapacityTranslation

/-! Active Taylor features of the actual v8 digit chart. The degree cut
uses a mixed ideal; it is not the nilpotence of each individual jet. -/
namespace V8CapacityFeatures
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityCRTJet V8CapacityTranslation

noncomputable section

variable {R H : Type*} [CommRing R] [Fintype H]

def shiftedPolynomial (p : R) (k : ℕ) (c : ℕ → R) : R[X] :=
  C (p*c 0) + X * ∑ j ∈ Finset.range (k-1), C (c (j+1)) * X^j

def rawFeature (p : R) (k : ℕ) (α : H → ℕ) (j : ℕ) (c : H → ℕ → R) : R :=
  (∏ i : H, shiftedPolynomial p k (c i) ^ α i : R[X]).coeff j

theorem in_mixed (p : R) (k : ℕ) (c : ℕ → R) :
    shiftedPolynomial p k c∈Ideal.span ({C p}:Set R[X]) ⊔ Ideal.span ({X}:Set R[X]) := by
  apply Submodule.mem_sup.mpr
  refine ⟨C (p*c 0),?_,X*∑ j ∈ Finset.range (k-1), C (c (j+1))*X^j,?_,rfl⟩
  · rw [Ideal.mem_span_singleton,map_mul]
    exact dvd_mul_right _ _
  · exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

/-- The minimum pi-factor estimate of part 1: this works symbolically in
the digit polynomial ring and survives arbitrary characteristic. -/
theorem feature_dvd (p : R) (k : ℕ) (α : H → ℕ) (j : ℕ) (c : H → ℕ → R) :
    p^((∑ i,α i)-j)∣ rawFeature p k α j c := by
  by_cases h : j<(∑ i,α i)
  · let I : Ideal R[X] := Ideal.span {C p}
    let J : Ideal R[X] := Ideal.span {X}
    let a := (∑ i,α i)-j
    have hmem : (∏ i : H, shiftedPolynomial p k (c i) ^ α i : R[X])∈
        (I ⊔ J)^(a+j) := by
      rw [show a+j=(∑ i,α i) by dsimp [a]; omega,← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (in_mixed p k (c i)) (α i))
    -- The sharp exponent a uses X rather than the generic m+n bound.
    have hstrong : (I ⊔ J)^(a+j) ≤ I^a ⊔ J^(j+1) := by
      rw [← Ideal.add_eq_sup,add_pow,Ideal.sum_eq_sup]
      apply Finset.sup_le
      intro u hu
      by_cases ha : a≤u
      · exact (Ideal.mul_le_right.trans (Ideal.mul_le_right.trans
          ((Ideal.pow_le_pow_right ha).trans le_sup_left)))
      · refine (Ideal.mul_le_right.trans (Ideal.mul_le_left.trans
          ((Ideal.pow_le_pow_right ?_).trans le_sup_right)))
        omega
    have hp := hstrong hmem
    rw [show I=Ideal.span ({C p}:Set R[X]) by rfl,show J=Ideal.span ({X}:Set R[X]) by rfl,
      Ideal.span_singleton_pow,Ideal.span_singleton_pow] at hp
    obtain ⟨u,hu,v,hv,hEq⟩ := Submodule.mem_sup.mp hp
    obtain ⟨u',hu'⟩ := Ideal.mem_span_singleton.mp hu
    obtain ⟨v',hv'⟩ := Ideal.mem_span_singleton.mp hv
    have hz : (X^(j+1)*v' : R[X]).coeff j=0 := by
      rw [Polynomial.coeff_X_pow_mul',if_neg (by omega)]
    unfold rawFeature
    rw [← hEq,hu',hv',Polynomial.coeff_add,hz,add_zero,← map_pow,Polynomial.coeff_C_mul]
    exact dvd_mul_right _ _
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h),pow_zero]
    exact one_dvd _

theorem coefficient_mk (k j : ℕ) (h : j<k) (g : R[X]) :
    coefficient R k j (AdjoinRoot.mk ((X:R[X])^k) g) = g.coeff j := by
  unfold coefficient
  rw [AdjoinRoot.modByMonicHom_mk]
  have hn := congrArg (fun a : R[X] => a.coeff j) (modByMonic_add_div g (monic_X.pow k))
  have hz : ((X:R[X])^k*(g /ₘ ((X:R[X])^k))).coeff j=0 := by
    rw [Polynomial.coeff_X_pow_mul',if_neg (by omega)]
  dsimp only at hn
  rwa [Polynomial.coeff_add,hz,add_zero] at hn

variable [IsLocalRing R]

omit [Fintype H] in
theorem finite_shift_is_mk (π : R) (P k : ℕ) (c : H → ℕ → R) (i : H) :
    digitShift R π P k c i =
      AdjoinRoot.mk ((X:(BaseMod R π P)[X])^k)
        ((shiftedPolynomial π k (c i)).map (coeffMod R π P)) := by
  simp only [digitShift,digitInput,map_zero,zero_add,shiftedPolynomial,Polynomial.map_add,
    Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C,Polynomial.map_sum,Polynomial.map_pow,
    map_add,map_mul,map_sum,map_pow,AdjoinRoot.mk_X,integralCoeff,RingHom.comp_apply,zJet]
  congr 1

theorem actual_feature (π : R) (P k : ℕ) (α : H → ℕ) (j : ℕ) (hj : j<k)
    (c : H → ℕ → R) :
    coefficient (BaseMod R π P) k j (∏ i : H, digitShift R π P k c i ^ α i) =
       coeffMod R π P (rawFeature π k α j c) := by
  let f : R[X] →+* FiniteJet R π P k :=
    (AdjoinRoot.mk ((X:(BaseMod R π P)[X])^k)).comp (Polynomial.mapRingHom (coeffMod R π P))
  have he (i : H) : digitShift R π P k c i=f (shiftedPolynomial π k (c i)) := finite_shift_is_mk π P k c i
  simp_rw [he,← map_pow]
  rw [← map_prod f]
  change coefficient (BaseMod R π P) k j (AdjoinRoot.mk ((X:(BaseMod R π P)[X])^k)
      ((∏ i : H, shiftedPolynomial π k (c i)^α i : R[X]).map (coeffMod R π P)))= _
  rw [coefficient_mk k j hj,Polynomial.coeff_map]
  rfl

theorem actual_feature_zero (π : R) (P k : ℕ) (α : H → ℕ) (j : ℕ) (hj : j<k)
    (c : H → ℕ → R) (hα : P+j≤∑ i,α i) :
    coefficient (BaseMod R π P) k j (∏ i : H, digitShift R π P k c i ^ α i)=0 := by
  rw [actual_feature π P k α j hj c,coeffMod,Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  exact (pow_dvd_pow π (by omega)).trans (feature_dvd π k α j c)

#print axioms in_mixed
#print axioms feature_dvd
#print axioms coefficient_mk
#print axioms finite_shift_is_mk
#print axioms actual_feature
#print axioms actual_feature_zero
end
end V8CapacityFeatures

