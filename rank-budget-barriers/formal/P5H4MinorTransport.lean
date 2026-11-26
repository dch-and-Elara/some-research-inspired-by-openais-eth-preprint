import RBSharp

/-! Determinantal divisors do not change under mutual polynomial generation.
The rectangular determinant expansion includes all address functions (not
just injections); repeated indices give identically zero minors. -/
namespace P5H4
open Matrix
open scoped BigOperators Classical Matrix

variable {S m n r : Type*} [CommRing S]

/-- Divisibility of every s-by-s minor. Using all row and column address
functions permits repetitions, which add only zero determinants. -/
def MinorDivisor (A : Matrix m n S) (s : ℕ) (d : S) : Prop :=
  ∀ (u : Fin s → m) (v : Fin s → n), d ∣ (A.submatrix u v).det

variable [Fintype r]

set_option maxHeartbeats 2900000 in
theorem determinant_expansion {i : Type*} [Fintype i] [DecidableEq i]
    (A : Matrix i r S) (B : Matrix r i S) :
    (A*B).det =
      ∑ f : i → r, (A.submatrix id f).det * ∏ j, B (f j) j := by
  calc
    _ = ∑ f : i → r, ∑ σ : Equiv.Perm i, (↑↑(Equiv.Perm.sign σ) : S) *
          ∏ j, A (σ j) (f j) * B (f j) j := by
      simp only [Matrix.det_apply',Matrix.mul_apply,Finset.prod_univ_sum,Finset.mul_sum,
        Fintype.piFinset_univ]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      rw [Matrix.det_apply',Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      simp only [Matrix.submatrix_apply,id_eq,Finset.prod_mul_distrib,mul_assoc]

theorem minorDivisor_right_mul (A : Matrix m r S) (B : Matrix r n S) (s : ℕ) (d : S)
    (h : MinorDivisor A s d) : MinorDivisor (A*B) s d := by
  intro u v
  have hm : (A*B).submatrix u v = A.submatrix u id * B.submatrix id v := by rfl
  rw [hm,determinant_expansion]
  apply Finset.dvd_sum
  intro f _
  exact (h u f).trans (dvd_mul_right _ _)

omit [Fintype r] in
theorem minorDivisor_transpose (A : Matrix m n S) (s : ℕ) (d : S) :
    MinorDivisor Aᵀ s d ↔ MinorDivisor A s d := by
  constructor
  · intro h u v
    have he : Aᵀ.submatrix v u = (A.submatrix u v)ᵀ := rfl
    rw [← Matrix.det_transpose (A.submatrix u v),← he]
    exact h v u
  · intro h u v
    have he : Aᵀ.submatrix u v = (A.submatrix v u)ᵀ := rfl
    rw [he,Matrix.det_transpose]
    exact h v u

theorem minorDivisor_left_mul (A : Matrix m r S) (B : Matrix r n S) (s : ℕ) (d : S)
    (h : MinorDivisor B s d) : MinorDivisor (A*B) s d := by
  apply (minorDivisor_transpose _ _ _).1
  rw [Matrix.transpose_mul]
  exact minorDivisor_right_mul Bᵀ Aᵀ s d ((minorDivisor_transpose _ _ _).2 h)

omit [Fintype r] in
/-- On a diagonal all minors have the same common divisors as the products
over injectively selected diagonal entries. This includes vanishing or
empty minors and needs no divisibility ordering of the diagonal. -/
theorem minorDivisor_diagonal {a : Type*} [DecidableEq a] (z : a → S) (s : ℕ) (d : S) :
    MinorDivisor (diagonal z) s d ↔
      ∀ u : Fin s → a, Function.Injective u → d ∣ ∏ i, z (u i) := by
  constructor
  · intro h u hu
    have hm : (diagonal z).submatrix u u = diagonal (fun i => z (u i)) := by
      apply Matrix.ext
      intro i j
      by_cases hij : i=j
      · subst j
        simp
      · simpa [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hij] using
          Matrix.diagonal_apply_ne z (hu.ne hij)
    simpa only [hm,Matrix.det_diagonal] using h u u
  · intro h u v
    by_cases hi : Function.Injective u
    · have hm : (diagonal z).submatrix u v = Matrix.of (fun i j =>
        z (u i) * (if u i=v j then (1:S) else 0)) := by
        apply Matrix.ext
        intro i j
        by_cases he : u i=v j <;> simp [he]
      rw [hm,Matrix.det_mul_column]
      exact (h u hi).trans (dvd_mul_right _ _)
    · obtain ⟨i,j,he,hne⟩ : ∃ i j, u i = u j ∧ i ≠ j := by
        simpa [Function.Injective,not_forall] using hi
      rw [Matrix.det_zero_of_row_eq hne (by funext a; simp [Matrix.submatrix_apply,he])]
      exact dvd_zero _

#print axioms determinant_expansion
#print axioms minorDivisor_right_mul
#print axioms minorDivisor_left_mul
#print axioms minorDivisor_diagonal
end P5H4
