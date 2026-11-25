import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Roots

/-!
The determinant degree budget used in the principal-subset rank argument.
This file formalizes the matrix-polynomial part; the group imbalance and
the subsequent probability and complexity estimates are separate results.
-/

open scoped BigOperators
open Polynomial Matrix

namespace Reconstruction
noncomputable section

variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

theorem det_degree_bound (A : Matrix n n F[X]) (d : ℕ)
    (hd : ∀ i j, (A i j).natDegree ≤ d) :
    A.det.natDegree ≤ Fintype.card n * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  apply (Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i : n, (A (σ i) i).natDegree ≤ ∑ _i : n, d :=
      Finset.sum_le_sum (fun i _ => hd (σ i) i)
    _ = Fintype.card n * d := by simp

theorem det_dvd_of_zero_rows (A : Matrix n n F[X]) (a : F) (s : Finset n)
    (hz : ∀ i ∈ s, ∀ j, (A i j).eval a = 0) :
    (X - C a) ^ s.card ∣ A.det := by
  classical
  let f : n → F[X] := fun i => if i ∈ s then X - C a else 1
  have hd : ∀ i j, f i ∣ A i j := by
    intro i j
    by_cases hi : i ∈ s
    · simpa only [f, if_pos hi, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
        using hz i hi j
    · simp [f, hi]
  choose B hB using hd
  have hA : A = Matrix.of (fun i j => f i * B i j) := by
    funext i j
    exact hB i j
  rw [hA, Matrix.det_mul_column]
  have hf : (∏ i : n, f i) = (X - C a) ^ s.card := by
    simp [f]
  rw [hf]
  exact dvd_mul_right _ _

theorem nullity_factor_dvd_det (A : Matrix n n F[X]) (a : F) :
    (X - C a) ^ (Fintype.card n - (A.map (Polynomial.eval a)).rank) ∣ A.det := by
  classical
  let M : Matrix n n F := A.map (Polynomial.eval a)
  obtain ⟨L, L', D, hD⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  let U : Matrix n n F := (L.map Matrix.TransvectionStruct.toMatrix).prod
  let V : Matrix n n F := (L'.map Matrix.TransvectionStruct.toMatrix).prod
  have hU : U.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hV : V.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L'
  let B : Matrix n n F[X] := U.map Polynomial.C * A * V.map Polynomial.C
  have heval : B.map (Polynomial.eval a) = Matrix.diagonal D := by
    change (Polynomial.evalRingHom a).mapMatrix
      (U.map Polynomial.C * A * V.map Polynomial.C) = Matrix.diagonal D
    rw [map_mul, map_mul]
    have hUe : (Polynomial.evalRingHom a).mapMatrix (U.map Polynomial.C) = U := by
      ext i j
      exact Polynomial.eval_C
    have hVe : (Polynomial.evalRingHom a).mapMatrix (V.map Polynomial.C) = V := by
      ext i j
      exact Polynomial.eval_C
    rw [hUe, hVe]
    exact hD
  have hUC : (U.map Polynomial.C).det = 1 := by
    change (Polynomial.C.mapMatrix U).det = 1
    rw [← RingHom.map_det, hU, map_one]
  have hVC : (V.map Polynomial.C).det = 1 := by
    change (Polynomial.C.mapMatrix V).det = 1
    rw [← RingHom.map_det, hV, map_one]
  have hdet : B.det = A.det := by
    simp only [B, Matrix.det_mul, hUC, hVC, one_mul, mul_one]
  have hrank : (Matrix.diagonal D).rank = M.rank := by
    calc
      (Matrix.diagonal D).rank = (U * M * V).rank := congrArg Matrix.rank hD.symm
      _ = (U * M).rank := Matrix.rank_mul_eq_left_of_isUnit_det V (U * M)
        (by rw [hV]; exact isUnit_one)
      _ = M.rank := Matrix.rank_mul_eq_right_of_isUnit_det U M
        (by rw [hU]; exact isUnit_one)
  let s := Finset.univ.filter (fun i => D i = 0)
  have hcard : s.card = Fintype.card n - M.rank := by
    rw [← hrank, Matrix.rank_diagonal]
    have h := Fintype.card_subtype_compl (fun i : n => D i ≠ 0)
    simpa [s, Fintype.card_subtype] using h
  have hz : ∀ i ∈ s, ∀ j, (B i j).eval a = 0 := by
    intro i hi j
    have hDi : D i = 0 := (Finset.mem_filter.mp hi).2
    have he := congrFun (congrFun heval i) j
    simpa [Matrix.map_apply, Matrix.diagonal_apply, hDi] using he
  have hd := det_dvd_of_zero_rows B a s hz
  rw [hdet, hcard] at hd
  exact hd

theorem determinant_nullity_budget {I : Type*} [Fintype I]
    (A : Matrix n n F[X]) (t : I → F) (d : ℕ)
    (ht : Function.Injective t) (hdet : A.det ≠ 0)
    (hd : ∀ i j, (A i j).natDegree ≤ d) :
    ∑ i : I, (Fintype.card n - (A.map (Polynomial.eval (t i))).rank)
      ≤ Fintype.card n * d := by
  classical
  let p := A.det
  let s : Finset F := Finset.univ.image t
  have hmult : ∀ i : I,
      Fintype.card n - (A.map (Polynomial.eval (t i))).rank
        ≤ Polynomial.rootMultiplicity (t i) p := by
    intro i
    exact (Polynomial.le_rootMultiplicity_iff hdet).mpr (nullity_factor_dvd_det A (t i))
  have hsum : (∑ i : I, Polynomial.rootMultiplicity (t i) p) =
      ∑ a ∈ s, p.roots.count a := by
    change (∑ i : I, Polynomial.rootMultiplicity (t i) p) =
      ∑ a ∈ Finset.univ.image t, p.roots.count a
    rw [Finset.sum_image (fun i _ j _ hij => ht hij)]
    simp only [Polynomial.count_roots]
  calc
    _ ≤ ∑ i : I, Polynomial.rootMultiplicity (t i) p :=
      Finset.sum_le_sum (fun i _ => hmult i)
    _ = ∑ a ∈ s, p.roots.count a := hsum
    _ ≤ ∑ a ∈ s ∪ p.roots.toFinset, p.roots.count a :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun _ _ _ => Nat.zero_le _)
    _ = p.roots.card := Multiset.sum_count_eq_card (by
      intro a ha
      exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha))
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ Fintype.card n * d := det_degree_bound A d hd

theorem normalized_nullity_budget {I : Type*} [Fintype I]
    (A : Matrix n n F[X]) (t : I → F) (d : ℕ)
    (ht : Function.Injective t)
    (hA0 : A.map (Polynomial.eval 0) = 1)
    (hd : ∀ i j, (A i j).natDegree ≤ d) :
    ∑ i : I, (Fintype.card n - (A.map (Polynomial.eval (t i))).rank)
      ≤ Fintype.card n * d := by
  have he : A.det.eval 0 = 1 := by
    change (Polynomial.evalRingHom 0) A.det = 1
    rw [RingHom.map_det]
    change (A.map (Polynomial.eval 0)).det = 1
    rw [hA0, Matrix.det_one]
  have hne : A.det ≠ 0 := by
    intro hz
    simp only [hz, Polynomial.eval_zero] at he
    exact zero_ne_one he
  exact determinant_nullity_budget A t d ht hne hd

#print axioms det_degree_bound
#print axioms det_dvd_of_zero_rows
#print axioms nullity_factor_dvd_det
#print axioms determinant_nullity_budget
#print axioms normalized_nullity_budget

end
end Reconstruction
