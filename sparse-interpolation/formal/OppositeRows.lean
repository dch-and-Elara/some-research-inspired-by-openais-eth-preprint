import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Ring.Parity

namespace SharpFactor

open Matrix Module

variable {F m n p : Type*} [Field F] [Fintype m] [Fintype n] [Fintype p]

private theorem rank_split_columns (A : Matrix m n F) (q : n → Prop) [DecidablePred q] :
    A.rank ≤ (A.submatrix id (Subtype.val : {j // q j} → n)).rank +
      Fintype.card {j // ¬ q j} := by
  classical
  let B := A.submatrix id (Subtype.val : {j // q j} → n)
  let C := A.submatrix id (Subtype.val : {j // ¬ q j} → n)
  let U := Submodule.span F (Set.range B.col)
  let V := Submodule.span F (Set.range C.col)
  have hs : Submodule.span F (Set.range A.col) ≤ U ⊔ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : q j
    · apply (show U ≤ U ⊔ V from le_sup_left)
      exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    · apply (show V ≤ U ⊔ V from le_sup_right)
      exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hle := Submodule.finrank_mono hs
  have hu : finrank F U = B.rank := (Matrix.rank_eq_finrank_span_cols B).symm
  have hv : finrank F V ≤ Fintype.card {j // ¬ q j} :=
    finrank_range_le_card C.col
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq U V
  change A.rank ≤ B.rank + _
  rw [← hu, Matrix.rank_eq_finrank_span_cols A]
  omega

private noncomputable def pairComb (l r : p ↪ m) (ε : F) : Matrix p m F := by
  classical
  exact Matrix.of fun i j => (if j = l i then 1 else 0) + ε * (if j = r i then 1 else 0)

omit [Fintype n] [Fintype p] in
private theorem pairComb_mul (l r : p ↪ m) (ε : F) (B : Matrix m n F) (i : p) (j : n) :
    (pairComb l r ε * B) i j = B (l i) j + ε * B (r i) j := by
  classical
  simp only [pairComb, Matrix.mul_apply, Matrix.of_apply, add_mul, mul_assoc,
    ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Independent sum or difference combinations of disjoint row pairs annihilate the
columns in q. This bounds the original rank using the number of columns outside q. -/
theorem paired_rows_rank_bound (A : Matrix m n F) (l r : p ↪ m)
    (hdisj : ∀ i j, l i ≠ r j) (ε : F) (q : n → Prop) [DecidablePred q]
    (hrow : ∀ i j, q j → A (l i) j + ε * A (r i) j = 0) :
    A.rank + Fintype.card p ≤ Fintype.card m + Fintype.card {j // ¬ q j} := by
  classical
  let D := pairComb l r ε
  let S : Matrix m p F := Matrix.of fun i j => if i = l j then 1 else 0
  have hDS : D * S = 1 := by
    ext i j
    change (pairComb l r ε * S) i j = _
    rw [pairComb_mul]
    simp [S, Matrix.one_apply, l.injective.eq_iff, Ne.symm (hdisj j i)]
  have hD : Fintype.card p ≤ D.rank := by
    have hle := Matrix.rank_mul_le_left D S
    rwa [hDS, Matrix.rank_one] at hle
  let B : Matrix m {j // q j} F := A.submatrix id Subtype.val
  have hDB : D * B = 0 := by
    ext i j
    change (pairComb l r ε * B) i j = _
    rw [pairComb_mul]
    exact hrow i j.1 j.2
  have hbound := Matrix.rank_add_rank_le_card_of_mul_eq_zero hDB
  have hsplit := rank_split_columns A q
  change A.rank ≤ B.rank + _ at hsplit
  omega

/-- A matrix of sampled monomials has rank deficiency at least the excess of the
number of opposite row pairs over the smaller exponent parity class. -/
theorem opposite_powers_rank_deficiency
    (x : m → F) (e : n → ℕ) (l r : p ↪ m)
    (hdisj : ∀ i j, l i ≠ r j) (hx : ∀ i, x (r i) = -x (l i)) :
    Fintype.card p -
        min (Fintype.card {j // Even (e j)}) (Fintype.card {j // Odd (e j)}) ≤
      Fintype.card m - (Matrix.of (fun i j => x i ^ e j) : Matrix m n F).rank := by
  classical
  let A : Matrix m n F := Matrix.of fun i j => x i ^ e j
  have hEven := paired_rows_rank_bound A l r hdisj (-1) (fun j => Even (e j))
    (fun i j hj => by simp [A, hx i, hj.neg_pow])
  have hOdd := paired_rows_rank_bound A l r hdisj 1 (fun j => Odd (e j))
    (fun i j hj => by simp [A, hx i, hj.neg_pow])
  have hodd : Fintype.card {j // ¬ Even (e j)} = Fintype.card {j // Odd (e j)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Nat.not_even_iff_odd))
  have heven : Fintype.card {j // ¬ Odd (e j)} = Fintype.card {j // Even (e j)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Nat.not_odd_iff_even))
  rw [hodd] at hEven
  rw [heven] at hOdd
  change _ ≤ Fintype.card m - A.rank
  omega

end SharpFactor
