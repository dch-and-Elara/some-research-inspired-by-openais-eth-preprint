import J6R9PacketCoeff
import Mathlib.Tactic

/-! Cancel the literal W_{xy} factor over the two-local integers.
Matching columns keep C-hat; all other columns remove the relevant
factor *before* reducing, with no forbidden rational inverse. -/
namespace J6R9PacketLocal
open scoped BigOperators Polynomial
open DenominatorBudget P1DyadicGrid P1DyadicGridBridge J6R9PacketCoeff
open Polynomial

noncomputable def factors (a : ℕ) (t : ℤ) (s : Finset ℤ) : TwoLocal[X] :=
  ∏ q ∈ s, (1+C (J6ActiveLocalFactor.slope a t q)*X)

noncomputable def W (a : ℕ) (t k : ℤ) : TwoLocal[X] :=
  if k=t then cHat a t else
    C (rho a t)*C (J6ActiveLocalFactor.slope a t k)*X*factors a t (((grid a).erase t).erase k)

noncomputable def printedW (a : ℕ) (k : ℤ) (T : ℚ) : ℚ :=
  (∏ q ∈ (grid a).erase k, (T-(q:ℚ))) /
    (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ)

theorem slope_rat {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈grid a) (hne : t≠q) :
    twoLocalRat (J6ActiveLocalFactor.slope a t q) = (2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ)) := by
  rw [J6ActiveLocalFactor.slope,dif_pos ⟨ht,hq,hne⟩]
  rfl

private theorem factors_rat {a : ℕ} {t : ℤ} (ht : t∈grid a)
    (s : Finset ℤ) (hs : s⊆(grid a).erase t) (z : ℚ) :
    (factors a t s).eval₂ twoLocalRat z =
      ∏ q ∈ s, (1+(2:ℚ)^(a+1)*z/((t:ℚ)-(q:ℚ))) := by
  let E := Polynomial.eval₂RingHom twoLocalRat z
  change E (factors a t s) = _
  rw [factors,map_prod]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [map_add,map_one,map_mul]
  change 1+(C (J6ActiveLocalFactor.slope a t q)).eval₂ twoLocalRat z *
    (X : TwoLocal[X]).eval₂ twoLocalRat z = _
  obtain ⟨hne,hqm⟩ := Finset.mem_erase.mp (hs hq)
  rw [Polynomial.eval₂_C,Polynomial.eval₂_X,slope_rat ht hqm hne.symm,div_mul_eq_mul_div]

private theorem raw_factors {a : ℕ} {t : ℤ} (s : Finset ℤ)
    (hs : s⊆(grid a).erase t) (z : ℚ) :
    (∏ q ∈ s, ((t:ℚ)+(2:ℚ)^(a+1)*z-(q:ℚ))) =
      (∏ q ∈ s, ((t:ℚ)-(q:ℚ)))*∏ q ∈ s, (1+(2:ℚ)^(a+1)*z/((t:ℚ)-(q:ℚ))) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hne : (t:ℚ)-(q:ℚ) ≠ 0 :=
    by exact_mod_cast sub_ne_zero.mpr (Finset.mem_erase.mp (hs hq)).1.symm
  field_simp
  ring

private theorem derivative_product {a : ℕ} {t : ℤ} (ht : t∈grid a) :
    (((cauchyPolynomial a).derivative.eval t : ℤ):ℚ) =
       ∏ q ∈ (grid a).erase t, ((t:ℚ)-(q:ℚ)) := by
  rw [cauchy_derivative_eval ht,Int.cast_prod]
  exact Finset.prod_congr rfl (fun q _ => Int.cast_sub t q)

theorem W_eval_rat {a : ℕ} {t k : ℤ} (ht : t∈grid a) (hk : k∈grid a) (z : ℚ) :
    (W a t k).eval₂ twoLocalRat z = printedW a k ((t:ℚ)+(2:ℚ)^(a+1)*z) := by
  classical
  have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) ≠ 0 :=
    by exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  by_cases h : k=t
  · subst k
    rw [W,if_pos rfl,cHat_eval_rat ht z,printedW,raw_factors _ (fun _ h => h) z,
      ← derivative_product ht]
    simp only [derivRatio,Int.cast_sub]
    field_simp
  · have hT : t∈(grid a).erase k := Finset.mem_erase.mpr ⟨Ne.symm h,ht⟩
    have hK : k∈(grid a).erase t := Finset.mem_erase.mpr ⟨h,hk⟩
    have hDiff : (t:ℚ)-(k:ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    have hSet : ((grid a).erase k).erase t=((grid a).erase t).erase k := by
      ext q
      simp [and_left_comm]
    have hP := Finset.mul_prod_erase ((grid a).erase t) (fun q : ℤ => (t:ℚ)-(q:ℚ)) hK
    rw [← derivative_product ht] at hP
    rw [W,if_neg h,Polynomial.eval₂_mul,Polynomial.eval₂_mul,Polynomial.eval₂_mul,
      Polynomial.eval₂_C,Polynomial.eval₂_C,Polynomial.eval₂_X,rho_rat ht,slope_rat ht hk (Ne.symm h),
      factors_rat ht _ (Finset.erase_subset _ _) z,printedW,
      ← Finset.mul_prod_erase ((grid a).erase k)
        (fun q : ℤ => ((t:ℚ)+(2:ℚ)^(a+1)*z-(q:ℚ))) hT,hSet,
      raw_factors _ (Finset.erase_subset _ _) z]
    unfold derivRatio
    rw [← hP]
    field_simp
    ring

/-- Literal normalization without division at the port's own mesh
point. The crossed denominator times its W entry is the same source
numerator, including at the canceled root. -/
theorem canceled_identity {a : ℕ} {k : ℤ} (hk : k∈grid a) (T : ℚ) :
    printedW a k T*(T-(k:ℚ)) =
      sourceNumerator a T / (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) := by
  rw [printedW,sourceNumerator,← Finset.mul_prod_erase (grid a) (fun q => T-(q:ℚ)) hk]
  ring

#print axioms W_eval_rat
#print axioms canceled_identity
end J6R9PacketLocal
