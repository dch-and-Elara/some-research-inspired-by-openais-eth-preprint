import SeparatedRank

/-!
# Rank with overlapping input views

Each product has four explicitly declared subsets: the row and column bits
read by its first factor and by its second. The two factors may freely overlap.
For an oriented base cut, the hazardous bits consist of row bits sent from the
first side to the second and column bits sent from the second side to the
first. All bounds below are for the original product functions over a field.
-/

namespace OverlappingRank

open scoped BigOperators
open SeparatedRank

/-- Each factor can read an arbitrary subset of each transversal. -/
structure ViewTerm (ι K : Type*) where
  firstRows : Finset ι
  firstCols : Finset ι
  secondRows : Finset ι
  secondCols : Finset ι
  coeff : K
  first : (firstRows → Bool) → (firstCols → Bool) → K
  second : (secondRows → Bool) → (secondCols → Bool) → K

namespace ViewTerm

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix entries are evaluated with the same assignment available to
overlapping coordinates in the two factors. -/
def matrix [Mul K] (t : ViewTerm ι K) : Matrix (ι → Bool) (ι → Bool) K :=
  Matrix.of fun x y =>
    t.coeff * t.first (CutTerm.restrict t.firstRows x) (CutTerm.restrict t.firstCols y) *
      t.second (CutTerm.restrict t.secondRows x) (CutTerm.restrict t.secondCols y)

/-- The first factor becomes row-local after fixing its column bits; the
second factor becomes column-local after fixing its row bits. -/
theorem rank_le_conditioned [Field K] (t : ViewTerm ι K) :
    t.matrix.rank ≤ 2 ^ (t.secondRows.card + t.firstCols.card) := by
  have h := conditioned_rank (CutTerm.restrict t.secondRows) (CutTerm.restrict t.firstCols)
    (fun r y => t.coeff * t.first (CutTerm.restrict t.firstRows r) y)
    (fun x c => t.second x (CutTerm.restrict t.secondCols c))
  change t.matrix.rank ≤ _ at h
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, ← pow_add] using h

/-- Hazardous row bits read by the second factor and hazardous column bits
read by the first. The opposite two directions are unrestricted. -/
def leakage (t : ViewTerm ι K) (rowPart colPart : Finset ι) : ℕ :=
  (t.secondRows ∩ rowPart).card + (t.firstCols \ colPart).card

/-- For the first side of the base cut, row excess minus hazardous leakage,
truncated below at zero. The views can be exchanged to choose the orientation. -/
def deficit (t : ViewTerm ι K) (rowPart colPart : Finset ι) : ℕ :=
  (rowPart.card - colPart.card) - t.leakage rowPart colPart

theorem deficit_le (t : ViewTerm ι K) (rowPart colPart : Finset ι) :
    t.deficit rowPart colPart ≤ Fintype.card ι := by
  exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Finset.card_le_univ rowPart))

/-- The termwise bound of equation (F), including the saturation at full
rank when all row excess is lost to leakage. -/
theorem rank_le_deficit [Field K] (t : ViewTerm ι K) (rowPart colPart : Finset ι) :
    t.matrix.rank ≤ 2 ^ (Fintype.card ι - t.deficit rowPart colPart) := by
  by_cases hd : t.deficit rowPart colPart = 0
  · simpa [hd] using t.matrix.rank_le_card_width
  have hrow : t.secondRows.card ≤ (t.secondRows ∩ rowPart).card + (Fintype.card ι - rowPart.card) := by
    have h : t.secondRows.card ≤ (t.secondRows \ rowPartᶜ).card + rowPartᶜ.card :=
      Finset.card_le_card_sdiff_add_card
    have hsets : t.secondRows \ rowPartᶜ = t.secondRows ∩ rowPart := by
      ext i
      simp
    simpa only [hsets, Finset.card_compl] using h
  have hcol : t.firstCols.card ≤ (t.firstCols \ colPart).card + colPart.card :=
    Finset.card_le_card_sdiff_add_card
  have hsize := Finset.card_le_univ rowPart
  apply t.rank_le_conditioned.trans (Nat.pow_le_pow_right (by decide) ?_)
  unfold deficit leakage at *
  omega

end ViewTerm

variable {ι J K : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Field K]

/-- An integer form of the capacity inequality, retaining each term's own
base cut, views and leakage. -/
theorem overlap_capacity (terms : J → ViewTerm ι K) (rows cols : J → Finset ι)
    (M : Matrix (ι → Bool) (ι → Bool) K) (hfull : M.rank = 2 ^ Fintype.card ι)
    (hsum : M = ∑ j, (terms j).matrix) :
    2 ^ Fintype.card ι ≤ ∑ j, 2 ^ (Fintype.card ι - (terms j).deficit (rows j) (cols j)) := by
  rw [← hfull, hsum]
  exact (rank_sum_le Finset.univ (fun j => (terms j).matrix)).trans
    (Finset.sum_le_sum fun j _ => (terms j).rank_le_deficit _ _)

/-- Dividing the integer budget by the dimension yields the exact rational
form of (F). -/
theorem overlap_weighted (terms : J → ViewTerm ι K) (rows cols : J → Finset ι)
    (M : Matrix (ι → Bool) (ι → Bool) K) (hfull : M.rank = 2 ^ Fintype.card ι)
    (hsum : M = ∑ j, (terms j).matrix) :
    (1 : ℚ) ≤ ∑ j, ((2 : ℚ) ^ (terms j).deficit (rows j) (cols j))⁻¹ := by
  let m := Fintype.card ι
  let d := fun j => (terms j).deficit (rows j) (cols j)
  have hbudget := overlap_capacity terms rows cols M hfull hsum
  have hq : (2 : ℚ) ^ m ≤ ∑ j, (2 : ℚ) ^ (m - d j) := by exact_mod_cast hbudget
  have hpos : 0 < (2 : ℚ) ^ m := pow_pos (by decide) _
  calc
    (1 : ℚ) = 2 ^ m / 2 ^ m := (div_self (ne_of_gt hpos)).symm
    _ ≤ (∑ j, (2 : ℚ) ^ (m - d j)) / 2 ^ m := div_le_div_of_nonneg_right hq hpos.le
    _ = ∑ j, ((2 : ℚ) ^ d j)⁻¹ := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hdm : d j ≤ m := (terms j).deficit_le _ _
      rw [← div_eq_mul_inv]
      apply (div_eq_iff (ne_of_gt hpos)).2
      have hpow : (2 : ℚ) ^ m = 2 ^ d j * 2 ^ (m - d j) := by
        rw [← pow_add, Nat.add_sub_of_le hdm]
      rw [hpow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by decide : (2 : ℚ) ≠ 0)), one_mul]

/-- A uniform lower bound for row excess and upper bound for hazardous
leakage force at least `2^(d-l)` terms. This also covers a zero deficit. -/
theorem overlap_barrier (terms : J → ViewTerm ι K) (rows cols : J → Finset ι)
    (M : Matrix (ι → Bool) (ι → Bool) K) (hfull : M.rank = 2 ^ Fintype.card ι)
    (hsum : M = ∑ j, (terms j).matrix) (d l : ℕ)
    (hexcess : ∀ j, d ≤ (rows j).card - (cols j).card)
    (hleak : ∀ j, (terms j).leakage (rows j) (cols j) ≤ l) :
    2 ^ (d - l) ≤ Fintype.card J := by
  classical
  let m := Fintype.card ι
  let e := fun j => (terms j).deficit (rows j) (cols j)
  have hbudget := overlap_capacity terms rows cols M hfull hsum
  have hgap (j : J) : d - l ≤ e j :=
    (Nat.sub_le_sub_right (hexcess j) _).trans (Nat.sub_le_sub_left (hleak j) _)
  cases isEmpty_or_nonempty J with
  | inl h => simp at hbudget
  | inr h =>
    have hdm : d - l ≤ m := (hgap h.some).trans ((terms h.some).deficit_le _ _)
    have hs : 2 ^ m ≤ Fintype.card J * 2 ^ (m - (d - l)) := by
      refine hbudget.trans ?_
      calc
        _ ≤ ∑ _j : J, 2 ^ (m - (d - l)) := Finset.sum_le_sum fun j _ =>
          Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (hgap j) _)
        _ = _ := by simp
    have hpow : 2 ^ (d - l) * 2 ^ (m - (d - l)) = 2 ^ m := by
      rw [← pow_add, Nat.add_sub_of_le hdm]
    exact Nat.le_of_mul_le_mul_right (hpow ▸ hs) (Nat.two_pow_pos _)

#print axioms ViewTerm.rank_le_conditioned
#print axioms ViewTerm.deficit_le
#print axioms ViewTerm.rank_le_deficit
#print axioms overlap_capacity
#print axioms overlap_weighted
#print axioms overlap_barrier

end OverlappingRank
