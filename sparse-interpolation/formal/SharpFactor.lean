import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Specialization rank and the determinant factor used in SHARP.md, step 2. -/

namespace SharpFactor

open Matrix Polynomial
open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Each column that vanishes at c contributes one copy of X - C c to the determinant. -/
theorem pow_X_sub_C_dvd_det_of_zero_columns
    (A : Matrix ι ι F[X]) (c : F) (s : Finset ι)
    (hs : ∀ j ∈ s, ∀ i, (A i j).eval c = 0) :
    (X - C c) ^ s.card ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  have h := Finset.prod_dvd_prod_of_dvd
    (s := (Finset.univ : Finset ι))
    (fun i => if i ∈ s then (X - C c) else 1)
    (fun i => A (σ i) i)
    (fun i _ => by
      change (if i ∈ s then X - C c else 1) ∣ A (σ i) i
      by_cases hi : i ∈ s
      · rw [if_pos hi, Polynomial.dvd_iff_isRoot]
        exact hs i hi (σ i)
      · simp [hi])
  simpa [Finset.prod_ite_mem] using h

/-- At a field point c, the determinant has an X - C c factor to at least
the specialization's rank deficiency. The statement includes identically zero determinants. -/
theorem pow_X_sub_C_dvd_det_of_rank
    (A : Matrix ι ι F[X]) (c : F) (d : ℕ)
    (h : (A.map (Polynomial.evalRingHom c)).rank + d ≤ Fintype.card ι) :
    (X - C c) ^ d ∣ A.det := by
  classical
  let A₀ := A.map (Polynomial.evalRingHom c)
  obtain ⟨l, r, w, hw⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal A₀
  let P := (l.map Matrix.TransvectionStruct.toMatrix).prod
  let Q := (r.map Matrix.TransvectionStruct.toMatrix).prod
  have hP : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod l
  have hQ : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod r
  change P * A₀ * Q = Matrix.diagonal w at hw
  let B := P.map Polynomial.C * A * Q.map Polynomial.C
  have hdet : B.det = A.det := by
    change (P.map Polynomial.C * A * Q.map Polynomial.C).det = A.det
    have hpmap : (P.map Polynomial.C).det = Polynomial.C P.det :=
      ((Polynomial.C : F →+* F[X]).map_det P).symm
    have hqmap : (Q.map Polynomial.C).det = Polynomial.C Q.det :=
      ((Polynomial.C : F →+* F[X]).map_det Q).symm
    rw [Matrix.det_mul, Matrix.det_mul, hpmap, hqmap, hP, hQ, map_one, one_mul, mul_one]
  have hPC : (P.map Polynomial.C).map (Polynomial.evalRingHom c) = P := by
    ext i j
    simp
  have hQC : (Q.map Polynomial.C).map (Polynomial.evalRingHom c) = Q := by
    ext i j
    simp
  have heval : B.map (Polynomial.evalRingHom c) = Matrix.diagonal w := by
    simpa only [B, Matrix.map_mul, hPC, hQC, A₀] using hw
  have hrank : (Matrix.diagonal w).rank = A₀.rank := by
    rw [← hw, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hQ ▸ isUnit_one),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP ▸ isUnit_one)]
  let s := Finset.univ.filter fun i => w i = 0
  have hsz : d ≤ s.card := by
    have hsum : s.card + Fintype.card {i // w i ≠ 0} = Fintype.card ι := by
      rw [Fintype.card_subtype_compl (p := fun i => w i = 0)]
      have hcard : s.card ≤ Fintype.card ι := Finset.card_le_univ s
      have hsub : Fintype.card {i // w i = 0} = s.card :=
        Fintype.card_subtype _
      rw [hsub]
      omega
    rw [← Matrix.rank_diagonal, hrank] at hsum
    change A₀.rank + d ≤ Fintype.card ι at h
    omega
  have hz (j : ι) (hj : j ∈ s) (i : ι) : (B i j).eval c = 0 := by
    have hwj : w j = 0 := (Finset.mem_filter.mp hj).2
    have hij := congrArg (fun M : Matrix ι ι F => M i j) heval
    by_cases hij' : i = j
    · subst i
      simpa [hwj] using hij
    · simpa [Matrix.diagonal_apply, hij'] using hij
  rw [← hdet]
  exact (pow_dvd_pow _ hsz).trans (pow_X_sub_C_dvd_det_of_zero_columns B c s hz)

/-- The full rank-deficiency exponent, with the natural-number convention at size zero. -/
theorem rank_deficiency_dvd_det
    (A : Matrix ι ι F[X]) (c : F) :
    (X - C c) ^ (Fintype.card ι - (A.map (Polynomial.evalRingHom c)).rank) ∣ A.det := by
  apply pow_X_sub_C_dvd_det_of_rank
  have := (A.map (Polynomial.evalRingHom c)).rank_le_card_width
  omega

end SharpFactor
