import S6Swap

namespace Section6

open Finset
set_option linter.unusedSectionVars false
open scoped BigOperators

variable {A I : Type*} [Fintype A] [LinearOrder A] [Fintype I] [DecidableEq I]

def negativeSet (t : WordCell I A) : Finset I := univ.filter fun i => (t i).2 < (t i).1

def orbitTags (u : WordCell I A) : Finset (WordCell I A) := univ.filter fun t =>
  ∀ i, samePair (u i) (t i)

def tagFrom (u : WordCell I A) (s : Finset I) : WordCell I A := fun i =>
  if (i ∈ s) = ((u i).2 < (u i).1) then u i else (u i).swap

lemma tagFrom_mem (u : WordCell I A) (s : Finset I) : tagFrom u s ∈ orbitTags u := by
  simp only [orbitTags, mem_filter, mem_univ, true_and, tagFrom]
  intro i
  split_ifs <;> simp [samePair]

lemma negativeSet_subset {u t : WordCell I A} (ht : t ∈ orbitTags u) :
    negativeSet t ⊆ unequal u := by
  simp only [orbitTags, mem_filter, mem_univ, true_and] at ht
  intro i hi
  have hi' : (t i).2 < (t i).1 := by simpa [negativeSet] using hi
  simpa [unequal] using (samePair_unequal (ht i)).2 (ne_of_gt hi')

lemma negativeSet_tagFrom {u : WordCell I A} {s : Finset I} (hs : s ⊆ unequal u) :
    negativeSet (tagFrom u s) = s := by
  ext i
  simp only [negativeSet, tagFrom, mem_filter, mem_univ, true_and]
  by_cases hi : i ∈ s
  · have hu : (u i).1 ≠ (u i).2 := by simpa [unequal] using hs hi
    rcases lt_or_gt_of_ne hu with hl | hl
    · simp [hi, hl, not_lt_of_gt hl]
    · simp [hi, hl]
  · by_cases hl : (u i).2 < (u i).1
    · simp [hi, hl, not_lt_of_gt hl]
    · simp [hi, hl]

lemma tagFrom_negativeSet {u t : WordCell I A} (ht : t ∈ orbitTags u) :
    tagFrom u (negativeSet t) = t := by
  simp only [orbitTags, mem_filter, mem_univ, true_and] at ht
  funext i
  rcases samePair_symm (ht i) with h | h
  · simp [tagFrom, negativeSet, h]
  · have hv : t i = (u i).swap := h
    by_cases he : (u i).1 = (u i).2
    · have hs : (u i).swap = u i := Prod.ext he.symm he
      simp [tagFrom, negativeSet, h, hs]
    · rcases lt_or_gt_of_ne he with hl | hl
      · simp [tagFrom, negativeSet, h, hl, not_lt_of_gt hl]
      · simp [tagFrom, negativeSet, h, hl, not_lt_of_gt hl]

theorem orbit_weight_count (u : WordCell I A) (j : ℕ) :
    ((orbitTags u).filter (fun t => weight t = j)).card = (unequal u).card.choose j := by
  rw [← card_powersetCard]
  apply card_bij (fun t _ => negativeSet t)
  · intro t ht
    rcases mem_filter.mp ht with ⟨ht, hw⟩
    exact mem_powersetCard.mpr ⟨negativeSet_subset ht, hw⟩
  · intro t ht s hs he
    rw [← tagFrom_negativeSet (mem_filter.mp ht).1,
        ← tagFrom_negativeSet (mem_filter.mp hs).1, he]
  · intro s hs
    rcases mem_powersetCard.mp hs with ⟨hsub, hcard⟩
    have he := negativeSet_tagFrom hsub
    have hw : weight (tagFrom u s) = j := by
      change (negativeSet (tagFrom u s)).card = j
      rw [he, hcard]
    exact ⟨tagFrom u s, mem_filter.mpr ⟨tagFrom_mem u s, hw⟩, he⟩

def fairTail (k : ℕ) (window : Finset ℕ) : ℚ :=
  ((∑ j ∈ (range (k + 1)).filter (· ∉ window), k.choose j : ℕ) : ℚ) / 2 ^ k

lemma orbit_exception_count (u : WordCell I A) (window : Finset ℕ) :
    ((orbitTags u).filter (fun t => weight t ∉ window)).card =
      ∑ j ∈ (range ((unequal u).card + 1)).filter (· ∉ window), (unequal u).card.choose j := by
  rw [sum_congr rfl (fun j _ => (orbit_weight_count u j).symm)]
  rw [sum_card_fiberwise_eq_card_filter]
  apply congrArg card
  ext t
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨ht, hw⟩
    exact ⟨ht, Nat.lt_succ_of_le (card_le_card (negativeSet_subset ht)), hw⟩
  · rintro ⟨ht, _, hw⟩
    exact ⟨ht, hw⟩

/-- The diagonal weight of the projection onto the actual retained Walsh rows. -/
theorem projection_diagonal (u : WordCell I A) (window : Finset ℕ) :
    ∑ t : {t : WordCell I A // weight t ∉ window}, walsh t.val u ^ 2 / energy t.val =
      fairTail (unequal u).card window := by
  classical
  have hterm (t : WordCell I A) :
      walsh t u ^ 2 / energy t =
        if t ∈ orbitTags u then 1 / (2 ^ (unequal u).card : ℚ) else 0 := by
    by_cases ht : t ∈ orbitTags u
    · have horb : ∀ i, samePair (u i) (t i) := by simpa [orbitTags] using ht
      have he : unequal t = unequal u := by
        ext i
        simp [unequal, samePair_unequal (horb i)]
      simp [ht, walsh_sq_of_support horb, energy_eq, he]
    · have hz : walsh t u = 0 := by
        by_contra hn
        exact ht (by simpa [orbitTags] using (walsh_ne_zero t u).mp hn)
      simp [ht, hz]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  have hc : ((univ : Finset {t : WordCell I A // weight t ∉ window}).filter
      (fun t => t.val ∈ orbitTags u)).card =
      ((orbitTags u).filter (fun t => weight t ∉ window)).card := by
    apply card_bij (fun t _ => t.val)
    · intro t ht
      exact mem_filter.mpr ⟨(mem_filter.mp ht).2, t.property⟩
    · intro t _ s _ h
      exact Subtype.ext h
    · intro t ht
      exact ⟨⟨t, (mem_filter.mp ht).2⟩, by simpa using (mem_filter.mp ht).1, rfl⟩
  rw [sum_const, nsmul_eq_mul, hc, orbit_exception_count]
  simp [fairTail, div_eq_mul_inv]

#print axioms orbit_weight_count
#print axioms projection_diagonal

end Section6


