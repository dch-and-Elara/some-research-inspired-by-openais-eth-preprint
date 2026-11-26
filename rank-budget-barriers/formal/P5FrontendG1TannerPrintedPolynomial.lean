import P5FrontendG1TannerPolynomial
import P5FrontendG1NormalizationRaw

/-! Identify the literal coefficient polynomial with the original product of
violation factors as a polynomial, not merely by equality of Boolean
evaluations. -/
namespace Paper5.FrontendG1.Tanner
open Paper5.FrontendG1.Normalization
open scoped BigOperators

theorem exponent_empty {W : Type*} [DecidableEq W] :
    exponent (∅ : Finset W)=0 := by
  ext w
  simp [exponent_apply]

theorem exponent_single {W : Type*} [DecidableEq W] (u : W) :
    exponent {u}=Finsupp.single u 1 := by
  ext w
  by_cases h : w=u <;> simp [exponent_apply,h]

theorem exponent_pair {W : Type*} [DecidableEq W] {u v : W} (h : u≠v) :
    exponent {u,v}=Finsupp.single u 1+Finsupp.single v 1 := by
  ext w
  by_cases h₁ : w=u
  · subst w
    simp [exponent_apply,h]
  · by_cases h₂ : w=v
    · subst w
      simp [exponent_apply,Ne.symm h]
    · simp [exponent_apply,h₁,h₂]

private theorem monomial_empty {W : Type*} [DecidableEq W] :
    (MvPolynomial.monomial (exponent (∅ : Finset W)) (1:F₂))=1 := by
  rw [exponent_empty,MvPolynomial.monomial_zero',map_one]

private theorem monomial_single {W : Type*} [DecidableEq W] (u : W) :
    (MvPolynomial.monomial (exponent {u}) (1:F₂))=MvPolynomial.X u := by
  rw [exponent_single,MvPolynomial.X]

private theorem monomial_pair {W : Type*} [DecidableEq W] {u v : W} (h : u≠v) :
    (MvPolynomial.monomial (exponent {u,v}) (1:F₂))=MvPolynomial.X u*MvPolynomial.X v := by
  simp [exponent_pair h,MvPolynomial.X]

section Source
variable {V : Type*} [DecidableEq V]

noncomputable def printedViolator (E : Finset (V×V)) (sgn : V→Bool) :
    GuardIndex E→MvPolynomial (GuardVar V) F₂
  | .inl v => 1+MvPolynomial.X (.inr v)
  | .inr (.inl v) => MvPolynomial.X (.inr v)*
      (MvPolynomial.X (.inl v)+MvPolynomial.C (zBit (sgn v)))
  | .inr (.inr e) => (1+MvPolynomial.X (.inl e.val.1))*(1+MvPolynomial.X (.inl e.val.2))

theorem violation_poly_is_printed (E : Finset (V×V)) (hS : OrientedSimple E)
    (sgn : V→Bool) (i : GuardIndex E) :
    violationPoly E sgn i=printedViolator E sgn i := by
  rcases i with v|(v|e)
  · simp [violationPoly,printedViolator,guardTerms,monomialList,monomial_empty,monomial_single]
  · have hZ : (Sum.inr v : GuardVar V)≠Sum.inl v := by simp
    cases hs : sgn v <;>
      simp [violationPoly,printedViolator,guardTerms,monomialList,monomial_single,
        monomial_pair hZ,zBit,hs,mul_add]
  · have hE : (Sum.inl e.val.1 : GuardVar V)≠Sum.inl e.val.2 := by
      exact fun hh => oriented_distinct hS e.property (Sum.inl_injective hh)
    simp only [violationPoly,printedViolator,guardTerms,monomialList,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,monomial_empty,monomial_single,monomial_pair hE]
    ring

theorem rowPoly_exact_printed_sum [Fintype V] (E : Finset (V×V)) (hS : OrientedSimple E)
    (sgn : V→Bool) (w : GuardIndex E→F₂) :
    rowPoly E sgn w=∑ i ∈ (Finset.univ : Finset (GuardIndex E)).filter (fun i=>w i=1),
      printedViolator E sgn i := by
  rw [rowPoly,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rcases binary_cases (w i) with h|h
  · simp [h]
  · simp [h,violation_poly_is_printed E hS]

end Source

#print axioms exponent_empty
#print axioms exponent_single
#print axioms exponent_pair
#print axioms violation_poly_is_printed
#print axioms rowPoly_exact_printed_sum
end Paper5.FrontendG1.Tanner