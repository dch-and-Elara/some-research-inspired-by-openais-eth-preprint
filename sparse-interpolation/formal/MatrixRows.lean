import Rows
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators fwdDiff

namespace SharpDifference

noncomputable def differenceWeight (i j : ℕ) : UPoly :=
  if j ≤ i then (((-1 : ℤ) ^ (i - j) * (i.choose j : ℤ)) : UPoly) else 0

noncomputable def differenceMatrix (k : ℕ) : Matrix (Fin k) (Fin k) UPoly :=
  Matrix.of fun i j => differenceWeight i.val j.val

noncomputable def sourceMatrix {k : ℕ} (E : Fin k → ℕ) : Matrix (Fin k) (Fin k) UPoly :=
  Matrix.of fun j l => (1 + (j.val : UPoly) * twoU) ^ E l

noncomputable def rowMatrix {k : ℕ} (M : ℕ) (E : Fin k → ℕ) :
    Matrix (Fin k) (Fin k) UPoly :=
  Matrix.of fun i l => liftPoly ((rowPoly M i.val).eval (E l : LocalPoly))

theorem det_differenceMatrix (k : ℕ) : (differenceMatrix k).det = 1 := by
  have ht : (differenceMatrix k).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have h : i.val < j.val := hij
    change differenceWeight i.val j.val = 0
    rw [differenceWeight, if_neg (Nat.not_le_of_lt h)]
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [differenceMatrix, differenceWeight]

theorem differenceMatrix_entry {k : ℕ} (E : Fin k → ℕ) (i l : Fin k) :
    (differenceMatrix k * sourceMatrix E) i l =
      (Δ_[1]^[i.val] (fun j : ℕ => (1 + (j : UPoly) * twoU) ^ E l)) 0 := by
  rw [Matrix.mul_apply, fwdDiff_iter_eq_sum_shift]
  change (∑ j : Fin k, differenceWeight i.val j.val *
      (1 + (j.val : UPoly) * twoU) ^ E l) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    differenceWeight i.val j * (1 + (j : UPoly) * twoU) ^ E l) k]
  calc
    _ = ∑ j ∈ Finset.range (i.val + 1), differenceWeight i.val j *
        (1 + (j : UPoly) * twoU) ^ E l := by
      symm
      apply Finset.sum_subset (Finset.range_mono i.isLt)
      intro j _ hj
      have h : ¬ j ≤ i.val := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
      simp [differenceWeight, h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have h : j ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      simp [differenceWeight, h, zsmul_eq_mul]

theorem differenceMatrix_mul_source {k : ℕ} (M : ℕ) (E : Fin k → ℕ)
    (hE : ∀ l, E l ≤ M) :
    differenceMatrix k * sourceMatrix E =
      Matrix.diagonal (fun i : Fin k => twoU ^ i.val) * rowMatrix M E := by
  ext i l
  rw [differenceMatrix_entry, fwdDiff_rowPoly M (E l) i.val (hE l),
    Matrix.diagonal_mul]
  rfl

theorem determinant_row_factor {k : ℕ} (M : ℕ) (E : Fin k → ℕ) (hE : ∀ l, E l ≤ M) :
    (sourceMatrix E).det = twoU ^ k.choose 2 * (rowMatrix M E).det := by
  have h := congrArg Matrix.det (differenceMatrix_mul_source M E hE)
  rw [Matrix.det_mul, det_differenceMatrix, one_mul, Matrix.det_mul,
    Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum] at h
  have he : (∑ i : Fin k, i.val) = k.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k,
      Finset.sum_range_id, Nat.choose_two_right]
  rwa [he] at h

theorem rowMatrix_common_truncation {k M N : ℕ} (E : Fin k → ℕ)
    (hM : ∀ l, E l ≤ M) (hN : ∀ l, E l ≤ N) : rowMatrix M E = rowMatrix N E := by
  apply Matrix.ext
  intro i l
  exact eval_rowPoly_common_truncation (i := i.val) (hM l) (hN l)

end SharpDifference

