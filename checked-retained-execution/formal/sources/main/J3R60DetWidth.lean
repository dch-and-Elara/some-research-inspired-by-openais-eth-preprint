import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

/-! Determinant witnesses give intermediate integer widths. The determinant
expansion is a *proof of the bound*, not an evaluated branch of the solver. -/
namespace J3R60
open scoped BigOperators

theorem natAbs_sum_bound {I : Type*} (g : I → ℤ) (s : Finset I) :
    (∑ i ∈ s, g i).natAbs ≤ ∑ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    exact (Int.natAbs_add_le ..).trans (Nat.add_le_add_left hs _)

theorem natAbs_prod_exact {I : Type*} (g : I → ℤ) (s : Finset I) :
    (∏ i ∈ s, g i).natAbs = ∏ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs => simp only [Finset.prod_insert hi, Int.natAbs_mul, hs]

def minorCap (T j : ℕ) : ℕ := j.factorial * T^j

theorem determinant_leibniz_height {K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix K K ℤ) (T : ℕ) (h : ∀ i j, (A i j).natAbs ≤ T) :
    A.det.natAbs ≤ minorCap T (Fintype.card K) := by
  rw [Matrix.det_apply']
  refine (natAbs_sum_bound _ _).trans ?_
  calc
    _ ≤ ∑ _σ : Equiv.Perm K, T^(Fintype.card K) := by
      apply Finset.sum_le_sum
      intro σ _
      rw [Int.natAbs_mul, natAbs_prod_exact]
      change (Equiv.Perm.sign σ : ℤ).natAbs * (∏ i, (A (σ i) i).natAbs) ≤
        T^(Fintype.card K)
      rw [Int.units_natAbs, one_mul]
      calc
        _ ≤ ∏ _i : K, T := Finset.prod_le_prod' (fun i _ => h (σ i) i)
        _ = _ := by simp
    _ = _ := by simp [minorCap, Fintype.card_perm]

theorem minorCap_mono_degree {T i j : ℕ} (hT : 1 ≤ T) (hij : i ≤ j) :
    minorCap T i ≤ minorCap T j :=
  Nat.mul_le_mul (Nat.factorial_le hij) (Nat.pow_le_pow_right hT hij)

theorem determinant_cap_bits (L j : ℕ) :
    minorCap (2^L) j ≤ 2^((L + Nat.clog 2 j)*j) := by
  calc
    _ ≤ j^j * (2^L)^j := Nat.mul_le_mul_right _ (Nat.factorial_le_pow j)
    _ ≤ (2^Nat.clog 2 j)^j * (2^L)^j := Nat.mul_le_mul_right _
      (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) j) j)
    _ = _ := by rw [← Nat.mul_pow, ← Nat.pow_add, ← Nat.pow_mul, Nat.add_comm]

/-- Two products and a subtraction at the stated input magnitude; all
forward update numerators in Bareiss have this shape. -/
theorem cross_numerator_height (a b c d : ℤ) (T : ℕ) (ha : a.natAbs ≤ T)
    (hb : b.natAbs ≤ T) (hc : c.natAbs ≤ T) (hd : d.natAbs ≤ T) :
    (a*b-c*d).natAbs ≤ 2*T^2 := by
  rw [sub_eq_add_neg]
  apply (Int.natAbs_add_le ..).trans
  simp only [Int.natAbs_neg, Int.natAbs_mul, pow_two, two_mul]
  exact Nat.add_le_add (Nat.mul_le_mul ha hb) (Nat.mul_le_mul hc hd)

#print axioms determinant_leibniz_height
#print axioms minorCap_mono_degree
#print axioms determinant_cap_bits
#print axioms cross_numerator_height

end J3R60
