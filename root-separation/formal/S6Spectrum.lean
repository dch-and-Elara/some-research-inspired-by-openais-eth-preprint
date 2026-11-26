import S6Cells
import Mathlib.Data.Nat.Choose.Sum

namespace Section6

open Finset
open scoped BigOperators Matrix
set_option linter.unusedSectionVars false

noncomputable section

variable {A I H : Type*} [Fintype A] [LinearOrder A] [Fintype I] [DecidableEq I]
  [Fintype H] [DecidableEq H]

def negativePairs (A : Type*) [Fintype A] [LinearOrder A] : Finset (A × A) :=
  univ.filter fun u => u.2 < u.1

def nonnegativePairs (A : Type*) [Fintype A] [LinearOrder A] : Finset (A × A) :=
  univ.filter fun u => ¬u.2 < u.1

theorem single_pair_counts :
    2 * (negativePairs A).card + Fintype.card A = Fintype.card A ^ 2 ∧
    (negativePairs A).card + (nonnegativePairs A).card = Fintype.card A ^ 2 := by
  classical
  let diagonalPairs : Finset (A × A) := univ.filter fun u => u.1 = u.2
  let positivePairs : Finset (A × A) := univ.filter fun u => u.1 < u.2
  have hc : (negativePairs A).card = positivePairs.card := by
    apply card_bij (fun u _ => u.swap)
    · intro u hu
      simpa [positivePairs, negativePairs] using hu
    · intro u _ v _ hv
      simpa using congrArg Prod.swap hv
    · intro u hu
      exact ⟨u.swap, by simpa [positivePairs, negativePairs] using hu, Prod.swap_swap _⟩
  have hd : diagonalPairs.card = Fintype.card A := by
    rw [← card_univ (α := A)]
    apply card_bij (fun u _ => u.1)
    · simp
    · intro a ha b hb h
      have ha' : a.1 = a.2 := (mem_filter.mp ha).2
      have hb' : b.1 = b.2 := (mem_filter.mp hb).2
      exact Prod.ext h (ha'.symm.trans (h.trans hb'))
    · intro a _
      exact ⟨(a,a), by simp [diagonalPairs], rfl⟩
  have he : nonnegativePairs A = diagonalPairs ∪ positivePairs := by
    ext u
    simp only [nonnegativePairs, diagonalPairs, positivePairs, mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl heq
    · rintro (h | h)
      · rw [h]
        exact lt_irrefl _
      · exact not_lt_of_gt h
  have hdis : Disjoint diagonalPairs positivePairs := by
    apply disjoint_left.mpr
    intro u hu hpu
    exact (ne_of_lt (mem_filter.mp hpu).2) (mem_filter.mp hu).2
  have hcom : nonnegativePairs A = (negativePairs A)ᶜ := by
    ext u
    simp [nonnegativePairs, negativePairs]
  have ht : (negativePairs A).card + (nonnegativePairs A).card = Fintype.card A ^ 2 := by
    rw [hcom, card_add_card_compl]
    simp [pow_two]
  refine ⟨?_, ht⟩
  rw [he, card_union_of_disjoint hdis, hd, ← hc] at ht
  omega

lemma negative_set_count (s : Finset I) :
    ((univ : Finset (WordCell I A)).filter fun t => negativeSet t = s).card =
      (negativePairs A).card ^ s.card * (nonnegativePairs A).card ^ (Fintype.card I - s.card) := by
  classical
  let labels (i : I) := if i ∈ s then negativePairs A else nonnegativePairs A
  have he : ((univ : Finset (WordCell I A)).filter fun t => negativeSet t = s) =
      Fintype.piFinset labels := by
    ext t
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro ht i
      have hi := Finset.ext_iff.mp ht i
      by_cases h : i ∈ s
      · simpa [labels, negativePairs, h, negativeSet] using hi.mpr h
      · have hh : i ∉ negativeSet t := fun hi' => h (hi.mp hi')
        simpa [labels, nonnegativePairs, h, negativeSet] using hh
    · intro h
      ext i
      specialize h i
      by_cases hm : i ∈ s <;> simpa [labels, negativePairs, nonnegativePairs, hm, negativeSet] using h
  rw [he, Fintype.card_piFinset]
  simp only [labels, apply_ite, prod_ite, filter_mem_eq_inter, univ_inter, prod_const,
    ]
  have hc : (univ.filter fun i : I => i ∉ s) = sᶜ := by ext i; simp
  rw [hc, card_compl]

theorem exceptional_row_count (window : Finset ℕ) :
    Fintype.card (Exceptional I A window) =
      ∑ j ∈ (range (Fintype.card I + 1)).filter (· ∉ window),
        (Fintype.card I).choose j * (negativePairs A).card ^ j *
          (nonnegativePairs A).card ^ (Fintype.card I - j) := by
  classical
  have hf (j : ℕ) :
      ((univ : Finset (WordCell I A)).filter fun t => weight t = j).card =
        (Fintype.card I).choose j * (negativePairs A).card ^ j *
          (nonnegativePairs A).card ^ (Fintype.card I - j) := by
    let targets := (univ : Finset I).powersetCard j
    have he := sum_card_fiberwise_eq_card_filter (univ : Finset (WordCell I A)) targets negativeSet
    have hh : ((univ : Finset (WordCell I A)).filter fun t => negativeSet t ∈ targets) =
        (univ.filter fun t => weight t = j) := by
      ext t
      simp [targets, mem_powersetCard, negativeSet, weight]
    rw [hh] at he
    rw [← he]
    simp_rw [negative_set_count]
    have hs (s : Finset I) (h : s ∈ targets) : s.card = j := (mem_powersetCard.mp h).2
    rw [sum_congr rfl (fun s h => by rw [hs s h]), sum_const, nsmul_eq_mul]
    simp [targets, card_powersetCard, mul_assoc]
  rw [Fintype.card_subtype, sum_congr rfl (fun j _ => (hf j).symm),
    sum_card_fiberwise_eq_card_filter]
  apply congrArg card
  ext t
  have h : weight t < Fintype.card I + 1 :=
    Nat.lt_succ_of_le (by simpa only [weight, card_univ] using card_filter_le (univ : Finset I) (fun i => (t i).2 < (t i).1))
  simp [h]

/-- The block matrix before incidence placement has exactly one independent
row for each exceptional tag in each copy. -/
theorem block_row_rank (window : Finset ℕ) :
    (show Matrix (H × Exceptional I A window) (H × WordCell I A) ℚ from fun b u =>
      blockWalsh b.1 b.2.val u).rank =
       Fintype.card H * Fintype.card (Exceptional I A window) := by
  classical
  let C : Matrix (H × Exceptional I A window) (H × WordCell I A) ℚ :=
    fun b u => blockWalsh b.1 b.2.val u
  let e (b : H × Exceptional I A window) := energy b.2.val
  have hC : C * Cᵀ = Matrix.diagonal e := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, C, e]
    simpa only [Prod.ext_iff, Subtype.coe_inj] using block_gram a.1 b.1 a.2.val b.2.val
  change C.rank = _
  rw [← C.rank_self_mul_transpose, hC, Matrix.rank_diagonal]
  have he (b : H × Exceptional I A window) : e b ≠ 0 := (energy_pos b.2.val).ne'
  simp [Fintype.card_subtype, he, Fintype.card_prod]

#print axioms single_pair_counts
#print axioms exceptional_row_count
#print axioms block_row_rank

end
end Section6


