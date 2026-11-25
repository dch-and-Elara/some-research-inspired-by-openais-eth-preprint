import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Local integer OR inversion and the exact exponent in a transversal flattening.
The global expander, palette and arithmetic DAG theorem is not formalized here. -/

namespace MatchingCore

def orMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 1]

def orInverse : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; 1, 0]

theorem or_left_inverse : orInverse * orMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, orMatrix, orInverse]

theorem or_right_inverse : orMatrix * orInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, orMatrix, orInverse]

theorem or_determinant : Matrix.det orMatrix = -1 := by
  norm_num [orMatrix, Matrix.det_fin_two]

theorem flatten_exponent (m a b : ℤ) :
    min a b + min (m - a) (m - b) = m - |a - b| := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_right (by omega), abs_of_nonpos (by omega)]
    omega
  · have h' : b ≤ a := by omega
    rw [min_eq_right h', min_eq_left (by omega), abs_of_nonneg (by omega)]
    omega

#print axioms or_left_inverse
#print axioms or_right_inverse
#print axioms or_determinant
#print axioms flatten_exponent

end MatchingCore
