import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
Integer heights for fraction-free elimination. Bounds apply to every
square submatrix of a rectangular matrix, including an augmented column.
-/

namespace BareissHeight

open scoped BigOperators

/-- Magnitude bound for both parts of the reduced rational representation. -/
def RatHeight (b : ℕ) (x : ℚ) : Prop :=
  x.num.natAbs ≤ 2^b ∧ x.den ≤ 2^b

theorem ratHeight_zero (b : ℕ) : RatHeight b 0 := by
  simp [RatHeight, Nat.one_le_two_pow]

theorem ratHeight_one (b : ℕ) : RatHeight b 1 := by
  simp [RatHeight, Nat.one_le_two_pow]

/-- The Leibniz height bound, uniform over row and column selections. -/
theorem minor_natAbs_le {R C K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix R C ℤ) (r : K → R) (c : K → C) (H : ℕ)
    (h : ∀ i j, (A i j).natAbs ≤ H) :
    (A.submatrix r c).det.natAbs ≤ (Fintype.card K).factorial * H ^ Fintype.card K := by
  let M := A.submatrix r c
  have ha (i j : K) : |M i j| ≤ (H:ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h (r i) (c j)
  have hb (σ : Equiv.Perm K) :
      |(Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i| ≤ (H:ℤ)^Fintype.card K := by
    rw [abs_mul, Equiv.Perm.sign_abs, one_mul, Finset.abs_prod]
    calc
      _ ≤ ∏ _i : K, (H:ℤ) := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => ha (σ i) i)
      _ = _ := by simp
  have hd : |M.det| ≤ ((Fintype.card K).factorial : ℤ) * (H:ℤ)^Fintype.card K := calc
    |M.det| ≤ ∑ σ : Equiv.Perm K, |(Equiv.Perm.sign σ : ℤ) * ∏ i, M (σ i) i| := by
      rw [Matrix.det_apply']
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm K, (H:ℤ)^Fintype.card K := Finset.sum_le_sum (fun σ _ => hb σ)
    _ = _ := by simp [Fintype.card_perm]
  rw [Int.abs_eq_natAbs] at hd
  exact_mod_cast hd

/-- A minor of order k fits in k(b+k)+1 magnitude bits when the input magnitude
is at most 2^b. The extra bit also covers the empty determinant. -/
theorem minor_lt_pow {R C K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix R C ℤ) (r : K → R) (c : K → C) (b : ℕ)
    (h : ∀ i j, (A i j).natAbs ≤ 2^b) :
    (A.submatrix r c).det.natAbs < 2^(Fintype.card K*(b+Fintype.card K)+1) := by
  let k := Fintype.card K
  refine (minor_natAbs_le A r c (2^b) h).trans_lt ?_
  calc
    k.factorial * (2^b)^k ≤ (2^k)^k * (2^b)^k := by
      apply Nat.mul_le_mul_right
      exact k.factorial_le_pow.trans (Nat.pow_le_pow_left k.lt_two_pow_self.le _)
    _ = 2^(k*(b+k)) := by rw [← mul_pow, ← pow_add, ← pow_mul, add_comm k b, Nat.mul_comm]
    _ < 2^(k*(b+k)+1) := by
      rw [pow_succ]
      have hp : 0 < (2:ℕ)^(k*(b+k)) := by positivity
      omega

/-- The minor bound expressed using the size of a binary natural number. -/
theorem minor_size_le {R C K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix R C ℤ) (r : K → R) (c : K → C) (b : ℕ)
    (h : ∀ i j, (A i j).natAbs ≤ 2^b) :
    (A.submatrix r c).det.natAbs.size ≤ Fintype.card K*(b+Fintype.card K)+1 :=
  Nat.size_le.mpr (minor_lt_pow A r c b h)

section
variable {R C : Type*} [Fintype C] [DecidableEq C]

/-- Positive row scaling, using the product of denominators including any RHS. -/
def rowDenominator (A : Matrix R C ℚ) (i : R) : ℕ :=
  ∏ j, (A i j).den

omit [DecidableEq C] in
theorem rowDenominator_pos (A : Matrix R C ℚ) (i : R) : 0 < rowDenominator A i := by
  exact Finset.prod_pos (fun j _ => (A i j).den_pos)

/-- Integer matrix obtained by clearing each row's rational denominators. -/
def clearRows (A : Matrix R C ℚ) : Matrix R C ℤ :=
  Matrix.of (fun i j => (A i j).num * (∏ k ∈ Finset.univ.erase j, ((A i k).den : ℤ)))

theorem clearRows_cast (A : Matrix R C ℚ) (i : R) (j : C) :
    ((clearRows A i j : ℤ) : ℚ) = (rowDenominator A i : ℚ) * A i j := by
  have hd : (rowDenominator A i : ℚ) =
      ((A i j).den : ℚ) * ∏ k ∈ Finset.univ.erase j, ((A i k).den : ℚ) := by
    rw [rowDenominator, Nat.cast_prod]
    exact (Finset.mul_prod_erase Finset.univ (fun k => ((A i k).den : ℚ))
      (Finset.mem_univ j)).symm
  have hq := (div_eq_iff (by exact_mod_cast (A i j).den_ne_zero :
    ((A i j).den : ℚ) ≠ 0)).mp (A i j).num_div_den
  simp only [clearRows, Matrix.of_apply, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
  rw [hd, mul_right_comm _ _ (A i j), mul_comm ((A i j).den : ℚ), ← hq]

theorem clearRows_natAbs_le (A : Matrix R C ℚ) (b : ℕ)
    (h : ∀ i j, RatHeight b (A i j)) (i : R) (j : C) :
    (clearRows A i j).natAbs ≤ 2 ^ (b * Fintype.card C) := by
  have hprod :
      (∏ k ∈ Finset.univ.erase j, (A i k).den) ≤ (2^b) ^ (Fintype.card C - 1) := by
    calc
      _ ≤ ∏ _k ∈ Finset.univ.erase j, (2:ℕ)^b :=
        Finset.prod_le_prod' (fun k _ => (h i k).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  have hc : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨j⟩
  have hd : (↑(∏ k ∈ Finset.univ.erase j, (A i k).den) : ℤ) =
      ∏ k ∈ Finset.univ.erase j, ((A i k).den : ℤ) := Nat.cast_prod _ _
  simp only [clearRows, Matrix.of_apply, Int.natAbs_mul, ← hd, Int.natAbs_natCast]
  calc
    _ ≤ 2^b * (2^b)^(Fintype.card C - 1) := Nat.mul_le_mul (h i j).1 hprod
    _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hc, pow_mul]

/-- Uniform minor size after clearing the denominators of the full row. -/
theorem clearRows_minor_size {K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix R C ℚ) (b : ℕ) (h : ∀ i j, RatHeight b (A i j))
    (r : K → R) (c : K → C) :
    ((clearRows A).submatrix r c).det.natAbs.size ≤
      Fintype.card K*(b*Fintype.card C+Fintype.card K)+1 :=
  minor_size_le (clearRows A) r c (b*Fintype.card C) (clearRows_natAbs_le A b h)

/-- The extra column `none` contains the right-hand side. -/
def augment (A : Matrix R C ℚ) (rhs : R → ℚ) : Matrix R (Option C) ℚ :=
  Matrix.of (fun i => Option.elim' (rhs i) (A i))

/-- The fractional and row-scaled integer equations have exactly the same
rational solution vectors. -/
theorem clearRows_system_iff (A : Matrix R C ℚ) (rhs : R → ℚ) (x : C → ℚ) :
    (∀ i, (∑ j, (clearRows (augment A rhs) i (some j) : ℚ) * x j) =
      (clearRows (augment A rhs) i none : ℚ)) ↔
      (∀ i, (∑ j, A i j * x j) = rhs i) := by
  simp only [clearRows_cast, augment, Matrix.of_apply, Option.elim'_some, Option.elim'_none,
    mul_assoc, ← Finset.mul_sum]
  apply forall_congr'
  intro i
  constructor
  · exact mul_left_cancel₀ (by exact_mod_cast (rowDenominator_pos (augment A rhs) i).ne')
  · exact congrArg ((rowDenominator (augment A rhs) i : ℚ) * ·)

end

end BareissHeight
