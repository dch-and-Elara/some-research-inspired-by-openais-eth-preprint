import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Common Boolean cube witness for final scalar families. -/

namespace RankBudget
open scoped BigOperators
open Matrix
variable {α K : Type*} [Fintype α] [DecidableEq α] [CommRing K]

/-- The incidence / zeta matrix on subsets, over any commutative ring. -/
def boolZeta (K : Type*) [Zero K] [One K] (a b : Finset α) : K :=
  if b ⊆ a then 1 else 0

omit [Fintype α] in
/-- The signed binomial expansion is exact in every characteristic. -/
theorem cubeExpansion (z : K) (A B : Finset α) :
    (1 - z) ^ (A ∩ B).card = ∑ S ∈ (A ∩ B).powerset, (-z) ^ S.card := by
  simpa [sub_eq_add_neg] using
    (Finset.prod_one_add (f := fun _ : α => -z) (A ∩ B))

/-- One fixed change of basis for every parameter. -/
theorem cubeZetaDiagonal (z : K) :
    (Matrix.of fun A B : Finset α => (1 - z) ^ (A ∩ B).card) =
      (Matrix.of (boolZeta K) * Matrix.diagonal (fun S : Finset α => (-z) ^ S.card)) *
         (Matrix.of (boolZeta K))ᵀ := by
  classical
  ext A B
  rw [Matrix.mul_apply, Matrix.of_apply, cubeExpansion]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, boolZeta, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  have hset : (Finset.univ.filter fun S : Finset α => S ⊆ A ∧ S ⊆ B) = (A ∩ B).powerset := by
    ext S; simp [Finset.subset_inter_iff]
  rw [← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> simp_all

/-- Incidence change of basis is unimodular: a permutation all of whose sets
increase by inclusion fixes every set. This proof does not order the Boolean lattice. -/
theorem boolZeta_det : (Matrix.of (boolZeta (α := α) K)).det = 1 := by
  classical
  nontriviality K
  rw [Matrix.det_apply, Finset.sum_eq_single (1 : Equiv.Perm (Finset α))]
  · simp [boolZeta]
  · intro σ _ hσ
    have hbad : ∃ s : Finset α, ¬ s ⊆ σ s := by
      by_contra! h
      apply hσ
      ext s i
      have hcard : ∀ a : Finset α, a.card = (σ a).card := by
        have hsum : (∑ a : Finset α, a.card) = ∑ a : Finset α, (σ a).card := by
          exact (Equiv.sum_comp σ Finset.card).symm
        exact fun a => (Finset.sum_eq_sum_iff_of_le
          (s := (Finset.univ : Finset (Finset α))) (fun s _ => Finset.card_le_card (h s))).mp
          hsum a (Finset.mem_univ _)
      have hs := Finset.eq_of_subset_of_card_le (h s) (hcard s).ge
      change i ∈ σ s ↔ i ∈ s
      rw [← hs]
    obtain ⟨s,hs⟩ := hbad
    have hz : (∏ i, Matrix.of (boolZeta (α := α) K) (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp [boolZeta,hs])
    rw [hz, smul_zero]
  · simp

/-- Exact determinant polynomial of the family over any commutative ring. -/
theorem cubeDet (z : K) :
    (Matrix.of fun A B : Finset α => (1 - z) ^ (A ∩ B).card).det =
      ∏ S : Finset α, (-z) ^ S.card := by
  rw [cubeZetaDiagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    boolZeta_det, Matrix.det_diagonal, one_mul, mul_one]

/-- Disjointness and every other nonzero field parameter have full rank over
that field, regardless of its characteristic. -/
theorem cubeFullRank {F : Type*} [Field F] (z : F) (hz : z ≠ 0) :
    (Matrix.of fun A B : Finset α => (1 - z) ^ (A ∩ B).card).rank = 2 ^ Fintype.card α := by
  classical
  have hdet : (Matrix.of fun A B : Finset α => (1 - z) ^ (A ∩ B).card).det ≠ 0 := by
    rw [cubeDet]
    exact Finset.prod_ne_zero_iff.mpr fun S _ => pow_ne_zero _ (neg_ne_zero.mpr hz)
  have hunit := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hdet)
  simpa using Matrix.rank_of_isUnit _ hunit

end RankBudget