import P5PrimitiveMinor
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators

/-! The finite matrix for multiplication by a polynomial matrix before
any residue or jet truncation. Its entries are proved to be the literal
convolution coefficients. Residue regularity implies injectivity over
the entire degree-admissible column window. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

variable {R : Type*} [CommRing R]
variable {I : Type*} [Fintype I]

noncomputable def testVec (m : ℕ) (x : I × Fin m → R) (i : I) : R[X] :=
  ∑ a : Fin m, Polynomial.monomial a.val (x (i,a))

omit [Fintype I] in
theorem testVec_coeff (m : ℕ) (x : I × Fin m → R) (i : I) (a : Fin m) :
    (testVec m x i).coeff a.val = x (i,a) := by
  unfold testVec
  rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single a]
  · simp
  · intro j _ hj
    have h : j.val ≠ a.val := fun e => hj (Fin.ext e)
    simp [Polynomial.coeff_monomial,h]
  · simp

def coefficientMatrix (A : Matrix I I R[X]) (m s : ℕ) :
    Matrix (I × Fin s) (I × Fin m) R :=
  fun i j => if j.2.val ≤ i.2.val then (A i.1 j.1).coeff (i.2.val-j.2.val) else 0

theorem coeff_mul_monomial_any (a : R[X]) (j l : ℕ) (x : R) :
    (a * Polynomial.monomial j x).coeff l =
      (if j≤l then a.coeff (l-j) else 0) * x := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,← mul_assoc,Polynomial.coeff_mul_X_pow']
  by_cases h : j≤l <;> simp [h,Polynomial.coeff_mul_C]

theorem mulVec_at_coeff (A : Matrix I I R[X]) (m : ℕ)
    (x : I × Fin m → R) (i : I) (l : ℕ) :
    ((A *ᵥ testVec m x) i).coeff l =
      ∑ j : I, ∑ a : Fin m,
        (if a.val≤l then (A i j).coeff (l-a.val) else 0)*x (j,a) := by
  simp only [Matrix.mulVec,dotProduct,testVec,Finset.mul_sum,Polynomial.finset_sum_coeff,
    coeff_mul_monomial_any]

theorem coefficientMatrix_mulVec (A : Matrix I I R[X]) (m s : ℕ)
    (x : I × Fin m → R) (i : I) (l : Fin s) :
    ((coefficientMatrix A m s) *ᵥ x) (i,l) = ((A *ᵥ testVec m x) i).coeff l.val := by
  rw [mulVec_at_coeff]
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,coefficientMatrix]

omit [Fintype I] in
theorem coefficientMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix I I R[X]) (m s : ℕ) :
    (coefficientMatrix A m s).map f = coefficientMatrix (A.map (Polynomial.mapRingHom f)) m s := by
  ext i j
  simp only [Matrix.map_apply,coefficientMatrix]
  by_cases h : j.2.val ≤ i.2.val <;> simp [h,Polynomial.coeff_map]

variable [IsDomain R] [DecidableEq I]

/-- Since the product degree stays below s, no lost high coefficient
can conceal a nonzero vector in the kernel of the coefficient matrix. -/
theorem coefficientMatrix_injective (A : Matrix I I R[X]) (m s d : ℕ)
    (hdegree : ∀ i j, (A i j).natDegree ≤ d) (hfit : m+d≤s)
    (hregular : A.det≠0) :
    Function.Injective (coefficientMatrix A m s).mulVecLin := by
  have hzero (x : I × Fin m → R) (hx : (coefficientMatrix A m s).mulVecLin x = 0) : x=0 := by
    have hz : A *ᵥ testVec m x = 0 := by
      funext i
      apply Polynomial.ext
      intro l
      change ((A *ᵥ testVec m x) i).coeff l = (0:R[X]).coeff l
      by_cases hl : l<s
      · rw [← coefficientMatrix_mulVec A m s x i ⟨l,hl⟩]
        exact congrFun hx (i,⟨l,hl⟩)
      · rw [mulVec_at_coeff,Polynomial.coeff_zero]
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro a _
        have ha := a.isLt
        have hs : a.val≤l := by omega
        have hp : (A i j).natDegree < l-a.val := (hdegree i j).trans_lt (by omega)
        rw [if_pos hs,Polynomial.coeff_eq_zero_of_natDegree_lt hp,zero_mul]
    have htsx : testVec m x = 0 := by
      by_contra hn
      exact hregular (Matrix.exists_mulVec_eq_zero_iff.mp ⟨testVec m x,hn,hz⟩)
    funext i
    have hh := congrArg (fun y : I → R[X] => (y i.1).coeff i.2.val) htsx
    simpa only [testVec_coeff,Pi.zero_apply,Polynomial.coeff_zero] using hh
  intro x y h
  have hsub : (coefficientMatrix A m s).mulVecLin (x-y) = 0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (hzero _ hsub)

variable [IsLocalRing R]

omit [IsDomain R] in
/-- This is exactly the primitive multiplication matrix step in (A.10):
the complement is an actual free module, and the first summand maps to
the untruncated polynomial product coefficient vector. -/
theorem polynomial_split_from_regular_residue (A : Matrix I I R[X]) (m s d : ℕ)
    (hdegree : ∀ i j, ((A i j).map (IsLocalRing.residue R)).natDegree ≤ d)
    (hfit : m+d≤s)
    (hregular : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0) :
    ∃ e : (((I × Fin m) → R) ×
      (Fin (Fintype.card (I × Fin s)-Fintype.card (I × Fin m))→R)) ≃ₗ[R] ((I × Fin s)→R),
      ∀ v, e (v,0) = (coefficientMatrix A m s).mulVecLin v := by
  apply exists_split_from_residue
  rw [coefficientMatrix_map]
  exact coefficientMatrix_injective _ m s d hdegree hfit hregular

#print axioms testVec_coeff
#print axioms mulVec_at_coeff
#print axioms coefficientMatrix_mulVec
#print axioms coefficientMatrix_map
#print axioms coefficientMatrix_injective
#print axioms polynomial_split_from_regular_residue
end Paper5
