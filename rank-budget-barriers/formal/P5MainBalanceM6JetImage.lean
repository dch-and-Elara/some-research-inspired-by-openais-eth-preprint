import P5MainBalanceOrderCap
import P5MainBalanceNative

/-! The native local computation can take place directly in the
iterated quotient. The final selector reads the original coefficient
and commutes with all previous ring operations. -/
namespace P5MainBalance.M6
open Polynomial P5MainBalance
open scoped BigOperators Classical

noncomputable def jetImage (ell J : ℕ) : Bivariate→+*P5A2.Double ℚ ell J :=
  (AdjoinRoot.mk ((X:(P5A2.Trunc ℚ ell)[X])^J)).comp
    (Polynomial.mapRingHom (AdjoinRoot.mk ((X:ℚ[X])^ell)))

private theorem trunc_pow_zero (R : Type*) [CommRing R] (n k : ℕ) (h : k≤n) :
    AdjoinRoot.mk ((X:R[X])^k) ((X:R[X])^n)=0 :=
  AdjoinRoot.mk_eq_zero.mpr (pow_dvd_pow _ h)

set_option maxHeartbeats 9400000 in
theorem jetImage_double_monomial (ell J : ℕ) (he : 0<ell) (s j : ℕ) (a : ℚ) :
    jetImage ell J (monomial j (monomial s a)) =
      if h : s<ell ∧ j<J then a • P5A2.pairBasis ell J he (⟨s,h.1⟩,⟨j,h.2⟩) else 0 := by
  let R := P5A2.Trunc ℚ ell
  let out := AdjoinRoot.mk ((X:R[X])^J)
  let inn := AdjoinRoot.mk ((X:ℚ[X])^ell)
  have hh :
      jetImage ell J (monomial j (monomial s a)) =
        algebraMap R (P5A2.Double ℚ ell J) (algebraMap ℚ R a * inn ((X:ℚ[X])^s)) *
          out ((X:R[X])^j) := by
    change out ((monomial j (monomial s a)).map inn)=_
    rw [Polynomial.map_monomial]
    rw [←C_mul_X_pow_eq_monomial,map_mul,AdjoinRoot.mk_C]
    congr 2
    rw [←C_mul_X_pow_eq_monomial,map_mul,AdjoinRoot.mk_C]
    rfl
  rw [hh]
  by_cases hs : s<ell
  · by_cases hj : j<J
    · rw [dif_pos ⟨hs,hj⟩,P5A2.pairBasis_apply]
      have hi : inn ((X:ℚ[X])^s)=P5A2.powers ℚ ell ⟨s,hs⟩ :=
        (P5A2.powers_apply ℚ ell ⟨s,hs⟩).symm
      have ho : out ((X:R[X])^j)=P5A2.outerPowers ell J he ⟨j,hj⟩ :=
        (@P5A2.powers_apply R _ (P5A2.trunc_nontrivial ℚ ell he) J ⟨j,hj⟩).symm
      rw [hi,ho,map_mul,Algebra.smul_def,IsScalarTower.algebraMap_apply ℚ R (P5A2.Double ℚ ell J),mul_assoc]
    · rw [dif_neg (fun h=>hj h.2)]
      rw [show out ((X:R[X])^j)=0 from trunc_pow_zero R j J (by omega),mul_zero]
  · rw [dif_neg (fun h=>hs h.1)]
    rw [show inn ((X:ℚ[X])^s)=0 from trunc_pow_zero ℚ s ell (by omega),mul_zero,map_zero,zero_mul]

set_option maxHeartbeats 12000000 in
theorem jetImage_exact_coefficient (ell J : ℕ) (he : 0<ell) (s : Fin ell) (j : Fin J)
    (p : Bivariate) :
    (P5A2.pairBasis ell J he).coord (s,j) (jetImage ell J p)=(p.coeff j).coeff s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,coeff_add] using congrArg₂ (·+·) hp hq
  | monomial m b =>
    induction b using Polynomial.induction_on' with
    | add b c hb hc =>
      simpa only [monomial_add,map_add,coeff_add] using congrArg₂ (·+·) hb hc
    | monomial n a =>
      rw [jetImage_double_monomial ell J he n m a]
      by_cases h : n<ell ∧ m<J
      · rw [dif_pos h,map_smul,P5A2.coord_basis]
        by_cases hm : m=j.val <;> by_cases hn : n=s.val
        · have hp : ((⟨n,h.1⟩ : Fin ell),(⟨m,h.2⟩ : Fin J))=(s,j) := Prod.ext (Fin.ext hn) (Fin.ext hm)
          rw [if_pos hp]
          simp [hm,hn]
        · have hp : ((⟨n,h.1⟩ : Fin ell),(⟨m,h.2⟩ : Fin J))≠(s,j) :=
            fun hh=>hn (congrArg (fun a : Fin ell×Fin J=>a.1.val) hh)
          rw [if_neg hp]
          simp only [coeff_monomial,if_pos hm,if_neg hn,smul_eq_mul,mul_zero]
        · have hp : ((⟨n,h.1⟩ : Fin ell),(⟨m,h.2⟩ : Fin J))≠(s,j) :=
            fun hh=>hm (congrArg (fun a : Fin ell×Fin J=>a.2.val) hh)
          rw [if_neg hp]
          simp only [coeff_monomial,if_neg hm,coeff_zero,smul_eq_mul,mul_zero]
        · have hp : ((⟨n,h.1⟩ : Fin ell),(⟨m,h.2⟩ : Fin J))≠(s,j) :=
            fun hh=>hm (congrArg (fun a : Fin ell×Fin J=>a.2.val) hh)
          rw [if_neg hp]
          simp only [coeff_monomial,if_neg hm,coeff_zero,smul_eq_mul,mul_zero]
      · rw [dif_neg h,map_zero]
        by_cases hm : m=j.val
        · have hn : n≠s.val := fun hns=>h ⟨hns.symm ▸ s.isLt,hm.symm ▸ j.isLt⟩
          simp [coeff_monomial,hm,hn]
        · simp [coeff_monomial,hm]

#print axioms jetImage_double_monomial
#print axioms jetImage_exact_coefficient
end P5MainBalance.M6
