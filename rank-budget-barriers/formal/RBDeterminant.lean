import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! Divisibility certificates for nonuniform budgeted interpolation.
The natural-degree bounds also hold when a permutation product vanishes. -/
namespace RankBudget
open Polynomial Matrix
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Leibniz product bound for a polynomial matrix with uniform entry degrees. -/
theorem detDegree_le (P : Matrix n n K[X]) (d : ℕ)
    (h : ∀ i j, (P i j).natDegree ≤ d) : P.det.natDegree ≤ Fintype.card n * d := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hs : ((Equiv.Perm.sign σ) • (∏ i, P (σ i) i)).natDegree =
      (∏ i, P (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with s | s
    · rw [s, one_smul]
    · rw [s, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
  rw [hs]
  refine (Polynomial.natDegree_prod_le Finset.univ fun i => P (σ i) i).trans ?_
  simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset n))
    (g := fun _ => d) fun i _ => h (σ i) i)

/-- A distinct-node list is represented by a finset of field elements.
A nonzero determinant polynomial may spend its root multiplicity only once. -/
theorem multiplicityBudget (p : K[X]) (hp : p ≠ 0) (s : Finset K) (e : K → ℕ)
    (he : ∀ t ∈ s, (X - C t) ^ e t ∣ p) : (∑ t ∈ s, e t) ≤ p.natDegree := by
  classical
  calc
    ∑ t ∈ s, e t ≤ ∑ t ∈ s, p.roots.count t := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Polynomial.count_roots]
      exact (Polynomial.le_rootMultiplicity_iff hp).2 (he t ht)
    _ ≤ ∑ t ∈ s ∪ p.roots.toFinset, p.roots.count t :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by intros; omega)
    _ = p.roots.card := Multiset.sum_count_eq_card fun a ha =>
      Finset.mem_union_right _ (Multiset.mem_toFinset.mpr ha)
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- A row-respecting local certificate after independent invertible row/column
changes. Different rows may have different guaranteed orders. The witness may
differ at every interpolation node. No Smith-normal-form existence is assumed. -/
theorem rowOrders_dvd (P U V W : Matrix n n K[X]) (t : K) (e : n → ℕ)
    (hu : IsUnit U.det) (hv : IsUnit V.det)
    (h : U * P * V = Matrix.of fun i j => (X - C t) ^ e i * W i j) :
    (X - C t) ^ (∑ i, e i) ∣ P.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum] at hd
  have hdvd : (X - C t) ^ (∑ i, e i) ∣ U.det * P.det * V.det := by
    rw [hd]
    exact dvd_mul_right _ _
  exact hu.dvd_mul_left.mp (hv.dvd_mul_right.mp hdvd)

/-- Global certified degree budget for independent, nonuniform local row orders. -/
theorem rowOrderBudget (P : Matrix n n K[X]) (d : ℕ) (s : Finset K) (e : K → n → ℕ)
    (pne : P.det ≠ 0) (degBound : ∀ i j, (P i j).natDegree ≤ d)
    (cert : ∀ t ∈ s, ∃ U V W : Matrix n n K[X], IsUnit U.det ∧ IsUnit V.det ∧
       U * P * V = Matrix.of fun i j => (X - C t) ^ e t i * W i j) :
    (∑ t ∈ s, ∑ i, e t i) ≤ Fintype.card n * d := by
  refine (multiplicityBudget P.det pne s (fun t => ∑ i, e t i) ?_).trans
    (detDegree_le _ _ degBound)
  intro t ht
  obtain ⟨U,V,W,hu,hv,h⟩ := cert t ht
  exact rowOrders_dvd _ U V W _ _ hu hv h

end RankBudget