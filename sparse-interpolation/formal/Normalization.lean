import MatrixRows
import Alternants

open scoped BigOperators

namespace SharpDifference

noncomputable def localRowMatrix {k : ℕ} (M : ℕ) (E : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) LocalPoly :=
  Matrix.of fun i j => (rowPoly M i.val).eval (E j : LocalPoly)

theorem map_localRowMatrix {k : ℕ} (M : ℕ) (E : Fin k → ℕ) :
    (localRowMatrix M E).map liftPoly = rowMatrix M E := rfl

theorem localRowMatrix_det_atZero {k M : ℕ} (E : Fin k → ℕ)
    (hM : ∀ i : Fin k, i.val ≤ M) :
    atZero (localRowMatrix M E).det = (Matrix.vandermonde (fun j => (E j : D))).det := by
  rw [RingHom.map_det]
  change ((localRowMatrix M E).map atZero).det = _
  have hmat : (localRowMatrix M E).map atZero =
      (Matrix.of (fun j i => (descPochhammer D i.val).eval (E j : D))).transpose := by
    apply Matrix.ext
    intro i j
    change atZero ((rowPoly M i.val).eval (E j : LocalPoly)) =
      (descPochhammer D i.val).eval (E j : D)
    rw [← Polynomial.eval₂_hom, ← Polynomial.eval_map, rowPoly_atZero M i.val (hM i),
      map_natCast]
  rw [hmat, Matrix.det_transpose]
  exact (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde _
    (fun i => descPochhammer D i.val) (fun i => descPochhammer_natDegree D i.val)
    (fun i => monic_descPochhammer D i.val)).symm

theorem eval_common_quotient {k M : ℕ} {Q : MvPolynomial (Fin k) LocalPoly}
    (hQ : (alternantMatrix (fun i : Fin k => rowPoly M i.val)).det = symbolicV k * Q)
    (E : Fin k → ℕ) :
    (localRowMatrix M E).det =
      (Matrix.vandermonde (fun j => (E j : LocalPoly))).det *
        MvPolynomial.eval (fun j => (E j : LocalPoly)) Q := by
  have h := congrArg (MvPolynomial.eval (fun j => (E j : LocalPoly))) hQ
  simpa only [localRowMatrix, eval_alternant_det, map_mul, eval_symbolicV] using h

theorem normalize_det_with_Q {k M : ℕ} {Q : MvPolynomial (Fin k) LocalPoly}
    (hQ : (alternantMatrix (fun i : Fin k => rowPoly M i.val)).det = symbolicV k * Q)
    (E : Fin k → ℕ) (hE : ∀ j, E j ≤ M) :
    (sourceMatrix E).det =
      twoU ^ k.choose 2 * liftPoly ((Matrix.vandermonde (fun j => (E j : LocalPoly))).det) *
        liftPoly (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) := by
  rw [determinant_row_factor M E hE, ← map_localRowMatrix]
  change twoU ^ k.choose 2 * (liftPoly.mapMatrix (localRowMatrix M E)).det = _
  rw [← RingHom.map_det, eval_common_quotient hQ, map_mul, mul_assoc]

theorem eval_vandermonde_atZero {k : ℕ} (E : Fin k → ℕ) :
    atZero ((Matrix.vandermonde (fun j => (E j : LocalPoly))).det) =
      (Matrix.vandermonde (fun j => (E j : D))).det := by
  rw [RingHom.map_det]
  change ((Matrix.vandermonde (fun j => (E j : LocalPoly))).map atZero).det = _
  congr 1
  apply Matrix.ext
  intro i j
  simp [Matrix.vandermonde_apply]

theorem normalized_atZero {k M : ℕ} {Q : MvPolynomial (Fin k) LocalPoly}
    (hQ : (alternantMatrix (fun i : Fin k => rowPoly M i.val)).det = symbolicV k * Q)
    (E : Fin k → ℕ) (hE : Function.Injective E) (hM : ∀ i : Fin k, i.val ≤ M) :
    atZero (MvPolynomial.eval (fun j => (E j : LocalPoly)) Q) = 1 := by
  have hv : (Matrix.vandermonde (fun j => (E j : D))).det ≠ 0 := by
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j h
    apply hE
    exact Nat.cast_injective h
  have he := congrArg atZero (eval_common_quotient hQ E)
  rw [localRowMatrix_det_atZero E hM, map_mul, eval_vandermonde_atZero] at he
  apply mul_left_cancel₀ hv
  simpa only [mul_one] using he.symm

end SharpDifference

