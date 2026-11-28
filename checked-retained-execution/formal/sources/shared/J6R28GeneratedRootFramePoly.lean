
import NativeProbeRing
import A1R10Monic

/-! Appendix D coefficient presentation: a monic leading one and
descending literal binary lower coefficients. The existing quotient
worker keeps the leading one implicit. -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial
open Polynomial
set_option maxHeartbeats 3000000

noncomputable def lowerBinary (R : Type*) [Semiring R] : List Bool→R[X]
  | [] => 0
  | b::bs => monomial bs.length (if b then 1 else 0)+lowerBinary R bs

noncomputable def binaryPolynomial (R : Type*) [Semiring R] (bs : List Bool) : R[X] :=
  monomial bs.length 1+lowerBinary R bs

theorem lower_binary_above (R : Type*) [Semiring R] (bs : List Bool) (j : ℕ)
    (hj : bs.length≤j) : (lowerBinary R bs).coeff j=0 := by
  induction bs with
  | nil => simp [lowerBinary]
  | cons b bs ih =>
    have ht : bs.length<j := by simpa only [List.length_cons] using hj
    rw [lowerBinary,coeff_add,coeff_monomial_of_ne _ ht.ne.symm,ih ht.le,add_zero]

theorem binary_monic_degree (R : Type*) [Semiring R] [Nontrivial R] (bs : List Bool) :
    (binaryPolynomial R bs).Monic ∧ (binaryPolynomial R bs).natDegree=bs.length := by
  have atHead : (binaryPolynomial R bs).coeff bs.length=1 := by
    simp [binaryPolynomial,lower_binary_above R bs bs.length]
  have h : (binaryPolynomial R bs).natDegree≤bs.length := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [binaryPolynomial,coeff_add,coeff_monomial_of_ne _ hj.ne.symm,lower_binary_above R bs j hj.le,add_zero]
  have hd := natDegree_eq_of_le_of_coeff_ne_zero h (atHead.trans_ne one_ne_zero)
  exact ⟨by simpa only [Monic,leadingCoeff,hd] using atHead,hd⟩

theorem lower_binary_coeff (R : Type*) [Semiring R] (bs : List Bool) (j : ℕ) :
    (lowerBinary R bs).coeff j=0 ∨ (lowerBinary R bs).coeff j=1 := by
  induction bs with
  | nil => exact Or.inl (by simp [lowerBinary])
  | cons b bs ih =>
    by_cases h : bs.length=j
    · subst j
      rw [lowerBinary,coeff_add,coeff_monomial,if_pos rfl,
        lower_binary_above R bs bs.length (Nat.le_refl _),add_zero]
      cases b <;> simp
    · rw [lowerBinary,coeff_add,coeff_monomial_of_ne _ (Ne.symm h),zero_add]
      exact ih

theorem binary_coeff_below (R : Type*) [Semiring R] (bs : List Bool) (j : ℕ)
    (hj : j<bs.length) :
    (binaryPolynomial R bs).coeff j=0 ∨ (binaryPolynomial R bs).coeff j=1 := by
  rw [binaryPolynomial,coeff_add,coeff_monomial_of_ne _ hj.ne,zero_add]
  exact lower_binary_coeff R bs j

theorem lower_binary_map {R S : Type*} [Semiring R] [Semiring S]
    (φ : R→+*S) (bs : List Bool) :
    (lowerBinary R bs).map φ=lowerBinary S bs := by
  induction bs with
  | nil => simp [lowerBinary]
  | cons b bs ih =>
    rw [lowerBinary,Polynomial.map_add,Polynomial.map_monomial,ih,lowerBinary]
    cases b <;> simp

theorem binary_polynomial_map {R S : Type*} [Semiring R] [Semiring S]
    (φ : R→+*S) (bs : List Bool) :
    (binaryPolynomial R bs).map φ=binaryPolynomial S bs := by
  simp only [binaryPolynomial,Polynomial.map_add,Polynomial.map_monomial,map_one,lower_binary_map]

structure LiteralPresentation (f : ℤ[X]) where
  lower : List Bool
  exactPolynomial : binaryPolynomial ℤ lower=f

theorem LiteralPresentation.monic {f : ℤ[X]} (data : LiteralPresentation f) : f.Monic :=
  data.exactPolynomial ▸ (binary_monic_degree ℤ data.lower).1

theorem LiteralPresentation.size {f : ℤ[X]} (data : LiteralPresentation f) :
    f.natDegree=data.lower.length :=
  (congrArg Polynomial.natDegree data.exactPolynomial).symm.trans (binary_monic_degree ℤ data.lower).2

theorem LiteralPresentation.coeff {f : ℤ[X]} (data : LiteralPresentation f) (j : ℕ)
    (hj : j<f.natDegree) : f.coeff j=0 ∨ f.coeff j=1 := by
  have ht : j<data.lower.length := data.size ▸ hj
  rw [←congrArg (fun Q : ℤ[X]=>Q.coeff j) data.exactPolynomial]
  exact binary_coeff_below ℤ data.lower j ht

#print axioms binary_monic_degree
#print axioms binary_coeff_below
#print axioms binary_polynomial_map
#print axioms LiteralPresentation.monic
#print axioms LiteralPresentation.size
#print axioms LiteralPresentation.coeff
end J6R28GeneratedRootFrame
