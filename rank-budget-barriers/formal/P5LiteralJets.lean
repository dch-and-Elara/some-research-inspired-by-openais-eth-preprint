import P5CyclicLength
import P5PolynomialSplit
import Mathlib.RingTheory.AdjoinRoot

/-! Literal P2 observations: substitute T=t+alpha*z, reduce coefficients
modulo pi^P, and reduce z modulo z^k in a genuine quotient ring. The
finite multiplication coefficient matrix commutes with this observation
even at non-unit scales and residue collisions. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

variable {R : Type*} [CommRing R] {I : Type*} [Fintype I]

abbrev LocalJet (π : R) (P k : ℕ) := AdjoinRoot (X^k : (Cyclic π P)[X])

noncomputable def nativeObs (π t α : R) (P k : ℕ) : R[X] →ₐ[R] LocalJet π P k :=
  Polynomial.aeval ((algebraMap R (LocalJet π P k)) t +
    (algebraMap R (LocalJet π P k)) α * AdjoinRoot.root (X^k : (Cyclic π P)[X]))

theorem nativeObs_X (π t α : R) (P k : ℕ) :
    nativeObs π t α P k X = (algebraMap R (LocalJet π P k)) t +
      (algebraMap R (LocalJet π P k)) α * AdjoinRoot.root (X^k : (Cyclic π P)[X]) := by
  simp [nativeObs]

theorem nativeObs_coefficient (π t α a : R) (P k : ℕ) :
    nativeObs π t α P k (C a) = (algebraMap R (LocalJet π P k)) a := by
  simp [nativeObs]

noncomputable def testVecLin (s : ℕ) (i : I) : (I × Fin s → R) →ₗ[R] R[X] where
  toFun x := testVec s x i
  map_add' x y := by
    simp only [testVec,Pi.add_apply,Polynomial.monomial_add,Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [testVec,Pi.smul_apply,Polynomial.smul_monomial,Finset.smul_sum,RingHom.id_apply]

omit [Fintype I] in
theorem testVec_other_coeff (s : ℕ) (x : I × Fin s→R) (i : I) (l : ℕ) (h : s≤l) :
    (testVec s x i).coeff l = 0 := by
  rw [testVec,Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro a _
  have hi : a.val ≠ l := by have h' := a.isLt; omega
  rw [Polynomial.coeff_monomial,if_neg hi]

theorem coefficientMatrix_exact_product (A : Matrix I I R[X]) (m s d : ℕ)
    (hdegree : ∀ i j, (A i j).natDegree≤d) (hfit : m+d≤s) (x : I × Fin m→R) :
    testVec s ((coefficientMatrix A m s) *ᵥ x) = A *ᵥ testVec m x := by
  funext i
  apply Polynomial.ext
  intro l
  by_cases hl : l<s
  · change (testVec s ((coefficientMatrix A m s) *ᵥ x) i).coeff (⟨l,hl⟩ : Fin s).val = _
    rw [testVec_coeff,coefficientMatrix_mulVec]
  · rw [testVec_other_coeff _ _ _ _ (by omega),mulVec_at_coeff]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro a _
    have ha := a.isLt
    have hs : a.val≤l := by omega
    have hp : (A i j).natDegree < l-a.val := (hdegree i j).trans_lt (by omega)
    rw [if_pos hs,Polynomial.coeff_eq_zero_of_natDegree_lt hp,zero_mul]

variable {T : Type*}

noncomputable def observeGrid (π : R) (t α : T→R) (P k : T→ℕ) (s : ℕ) :
    (I × Fin s→R) →ₗ[R] (∀ u : T, I→LocalJet π (P u) (k u)) :=
  LinearMap.pi fun u => LinearMap.pi fun i =>
    (nativeObs π (t u) (α u) (P u) (k u)).toLinearMap.comp (testVecLin s i)

noncomputable def localMul (A : Matrix I I R[X]) (π t α : R) (P k : ℕ) :
    (I→LocalJet π P k) →ₗ[R] (I→LocalJet π P k) :=
  ((A.map (nativeObs π t α P k).toRingHom).mulVecLin).restrictScalars R

theorem observed_mul (A : Matrix I I R[X]) (π : R) (t α : T→R) (P k : T→ℕ) (m s d : ℕ)
    (hdegree : ∀ i j, (A i j).natDegree≤d) (hfit : m+d≤s)
    (x : I × Fin m→R) (u : T) :
    observeGrid π t α P k s ((coefficientMatrix A m s) *ᵥ x) u =
      localMul A π (t u) (α u) (P u) (k u) (observeGrid π t α P k m x u) := by
  have he := coefficientMatrix_exact_product A m s d hdegree hfit x
  change (fun i => nativeObs π (t u) (α u) (P u) (k u)
      (testVec s ((coefficientMatrix A m s) *ᵥ x) i)) =
    (A.map (nativeObs π (t u) (α u) (P u) (k u)).toRingHom) *ᵥ
      (fun i => nativeObs π (t u) (α u) (P u) (k u) (testVec m x i))
  rw [he]
  funext i
  exact RingHom.map_mulVec (nativeObs π (t u) (α u) (P u) (k u)).toRingHom A (testVec m x) i

#print axioms nativeObs_X
#print axioms nativeObs_coefficient
#print axioms testVecLin
#print axioms testVec_other_coeff
#print axioms coefficientMatrix_exact_product
#print axioms observed_mul
end Paper5
