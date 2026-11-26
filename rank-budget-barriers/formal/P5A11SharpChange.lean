import P5A11SharpNewton
import Mathlib.LinearAlgebra.Matrix.Block

/-! Actual monomial-to-monic-degree basis conversion for confluent
Hasse evaluation. The matrix product is proved entrywise. The concrete
Newton block order's ordinal enumeration is a separate interface. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical
variable {R : Type*} [CommRing R]

noncomputable def basisHasseMatrix {n : ℕ} (t a : Fin n→R) (j : Fin n→ℕ)
    (p : Fin n→R[X]) : Matrix (Fin n) (Fin n) R :=
  fun i i' => (affinePolynomial (t i) (a i) (p i')).coeff (j i)

noncomputable def monomialHasseMatrix {n : ℕ} (t a : Fin n→R) (j : Fin n→ℕ) :
    Matrix (Fin n) (Fin n) R := basisHasseMatrix t a j (fun i=>X^i.val)

noncomputable def basisCoefficients {n : ℕ} (p : Fin n→R[X]) :
    Matrix (Fin n) (Fin n) R := Matrix.of (fun i j => (p j).coeff i.val)

theorem basisHasse_matrix_product {n : ℕ} (t a : Fin n→R) (j : Fin n→ℕ)
    (p : Fin n→R[X]) (hd : ∀ i,(p i).natDegree<n) :
    basisHasseMatrix t a j p = monomialHasseMatrix t a j * basisCoefficients p := by
  ext u v
  have h : p v = ∑ i : Fin n,C ((p v).coeff i.val)*X^i.val := by
    let f (a : ℕ) := C ((p v).coeff a)*X^a
    change p v=∑ i : Fin n,f i.val
    rw [Fin.sum_univ_eq_sum_range f n]
    exact (p v).as_sum_range_C_mul_X_pow' (hd v)
  change (affinePolynomial (t u) (a u) (p v)).coeff (j u) =
    ∑ i : Fin n,(affinePolynomial (t u) (a u) (X^i.val)).coeff (j u)*(p v).coeff i.val
  nth_rw 1 [h]
  rw [map_sum,finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  have hC : affinePolynomial (t u) (a u) (C ((p v).coeff i.val)) = C ((p v).coeff i.val) := by
    change (C ((p v).coeff i.val)).comp (C (t u)+C (a u)*X) = _
    exact C_comp
  rw [map_mul,hC,coeff_C_mul,mul_comm]

theorem basisHasse_det_monic {n : ℕ} (t a : Fin n→R) (j : Fin n→ℕ)
    (p : Fin n→R[X]) (hd : ∀ i,(p i).natDegree=i.val) (hm : ∀ i,(p i).Monic) :
    (basisHasseMatrix t a j p).det = (monomialHasseMatrix t a j).det := by
  rw [basisHasse_matrix_product t a j p (fun i=>(hd i).trans_lt i.isLt),Matrix.det_mul]
  have h : (basisCoefficients p).det=1 := Matrix.det_matrixOfPolynomials p hd hm
  rw [h,mul_one]

#print axioms basisHasse_matrix_product
#print axioms basisHasse_det_monic
end Paper5
