import RBSharp

/-! Equality criteria in H.6 that are independent of the normal-form
existence proof: clipping equality and the leading matrix at a fixed grade. -/
namespace P5H4
open Polynomial Matrix
open scoped BigOperators

variable {I K n : Type*}

/-- A finite clipped sum loses nothing exactly when every order is within
its cap, including zero caps and an empty observation. -/
theorem clipped_eq_iff [Fintype n] (s : Finset I) (k : I → ℕ) (e : I → n → ℕ) :
    (∑ t ∈ s, ∑ i, min (k t) (e t i)) = ∑ t ∈ s, ∑ i, e t i ↔
      ∀ t ∈ s, ∀ i, e t i ≤ k t := by
  constructor
  · intro heq t ht i
    by_contra h
    have hin : (∑ j, min (k t) (e t j)) < ∑ j, e t j :=
      Finset.sum_lt_sum (fun j _ => min_le_right ..)
        ⟨i, Finset.mem_univ i, by omega⟩
    have hout : (∑ u ∈ s, ∑ j, min (k u) (e u j)) < ∑ u ∈ s, ∑ j, e u j :=
      Finset.sum_lt_sum (fun u _ => Finset.sum_le_sum (fun j _ => min_le_right ..))
        ⟨t, ht, hin⟩
    omega
  · intro h
    exact Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun i _ =>
      min_eq_right (h t ht i)

variable [Field K] [Fintype n] [DecidableEq n]

/-- The scalar at degree N*d is precisely the determinant of the grade-d
coefficient matrix; zero polynomial entries need no separate convention. -/
theorem det_grade_coeff (A : Matrix n n K[X]) (d : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.coeff (Fintype.card n * d) =
      (A.map fun p => p.coeff d).det := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_smul, ← Finset.card_univ,
    Polynomial.coeff_prod_of_natDegree_le Finset.univ _ _ (fun i _ => h (σ i) i)]
  rfl

theorem det_grade_bound (A : Matrix n n K[X]) (d : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d) : A.det.natDegree ≤ Fintype.card n * d := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ (fun σ _ => ?_)
  apply (Polynomial.natDegree_smul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : n, d :=
      Finset.sum_le_sum (fun i _ => h (σ i) i)
    _ = _ := by simp

/-- The final inequality of (H.6) is attained iff the chosen grade's leading
coefficient matrix is nonsingular, for a regular square polynomial matrix. -/
theorem det_grade_eq_iff (A : Matrix n n K[X]) (d : ℕ)
    (hA : A.det ≠ 0) (h : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.natDegree = Fintype.card n * d ↔ (A.map fun p => p.coeff d).det ≠ 0 := by
  rw [← det_grade_coeff A d h]
  constructor
  · intro he
    rw [← he, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hA
  · intro he
    have hb := det_grade_bound A d h
    by_contra hn
    exact he (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hb hn))

#print axioms clipped_eq_iff
#print axioms det_grade_coeff
#print axioms det_grade_bound
#print axioms det_grade_eq_iff
end P5H4
