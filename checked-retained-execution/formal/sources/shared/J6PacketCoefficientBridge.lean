import J6ChildIdentity
import J6RecursiveModes

namespace J6PacketCoefficientBridge
open scoped Classical BigOperators
open MvPolynomial J6ActiveProfile

variable {R I M : Type*} [CommRing R] [Fintype I] [Fintype M]

noncomputable def exponent (v : Option M) : M →₀ ℕ :=
  v.elim' 0 (fun m => Finsupp.single m 1)

omit [Fintype I] [Fintype M] [CommRing R] in
theorem exponent_apply (v : Option M) (m : M) :
    exponent v m = if v = some m then 1 else 0 := by
  classical
  cases v with
  | none => simp [exponent]
  | some n => simp [exponent, Finsupp.single_apply]

omit [Fintype M] [CommRing R] in
theorem exponent_sum (x : I → Option M) (m : M) :
    (∑ i, exponent (x i)) m = count x m := by
  classical
  rw [Finsupp.finset_sum_apply]
  simp only [exponent_apply, count]
  rw [← Finset.sum_filter]
  simp

omit [Fintype I] [Fintype M] in
theorem prod_monomials (s : Finset I) (x : I → Option M) (f : I → Option M → R) :
    (∏ i ∈ s, monomial (exponent (x i)) (f i (x i))) =
      monomial (∑ i ∈ s, exponent (x i)) (∏ i ∈ s, f i (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih, MvPolynomial.monomial_mul]

/-- The finite row-allocation extraction equals literal polynomial
coefficient extraction; no free coefficient oracle is needed for this identity. -/
theorem coeff_allocations (f : I → Option M → R) (beta : M →₀ ℕ) :
    coeff beta (∏ i, ∑ v : Option M, monomial (exponent v) (f i v)) =
      ∑ x : I → Option M,
        if ∀ m, count x m = beta m then ∏ i, f i (x i) else 0 := by
  classical
  rw [Fintype.prod_sum, coeff_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [prod_monomials, coeff_monomial]
  have heq : (∑ i, exponent (x i)) = beta ↔ ∀ m, count x m = beta m := by
    constructor
    · intro h m
      rw [← exponent_sum x m, h]
    · intro h
      ext m
      rw [exponent_sum, h m]
  simp only [heq]

#print axioms exponent_apply
#print axioms exponent_sum
#print axioms prod_monomials
#print axioms coeff_allocations
end J6PacketCoefficientBridge
