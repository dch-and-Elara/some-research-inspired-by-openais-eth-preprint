import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Section6

open scoped BigOperators
set_option linter.unusedSectionVars false

variable {A : Type*} [Fintype A] [LinearOrder A]
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev WordCell (I A : Type*) := I → A × A

/-- An ascending unequal tag is the symmetric row, a descending tag
is the antisymmetric row, and a repeated symbol is the singleton row. -/
def swapEntry (tag u : A × A) : ℚ :=
  if u = tag then (if tag.1 ≤ tag.2 then 1 else -1)
  else if u = tag.swap then 1 else 0

def samePair (u v : A × A) : Prop := u = v ∨ u = v.swap

instance (u v : A × A) : Decidable (samePair u v) :=
  inferInstanceAs (Decidable (_ ∨ _))

lemma swapEntry_ne_zero (tag u : A × A) :
    swapEntry tag u ≠ 0 ↔ samePair u tag := by
  unfold swapEntry samePair
  split_ifs <;> simp_all

lemma swapEntry_sq (tag u : A × A) :
    swapEntry tag u ^ 2 = if samePair u tag then 1 else 0 := by
  unfold swapEntry samePair
  split_ifs <;> norm_num <;> simp_all

lemma samePair_symm {u v : A × A} (h : samePair u v) : samePair v u := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, Prod.swap_swap])

lemma samePair_trans {u v w : A × A} (h : samePair u v) (j : samePair v w) :
    samePair u w := by
  rcases h with h | h <;> rcases j with j | j <;>
    subst u <;> subst v <;> simp [samePair]

def pairSize (u : A × A) : ℚ := if u.1 = u.2 then 1 else 2

lemma gram_swapEntry (t s : A × A) :
    ∑ u, swapEntry t u * swapEntry s u = if t = s then pairSize t else 0 := by
  classical
  have hsupport (u : A × A) (hu : u ∉ ({t, t.swap} : Finset (A × A))) :
      swapEntry t u = 0 := by
    by_contra hn
    exact hu (by simpa [samePair, Finset.mem_insert, Finset.mem_singleton] using
      (swapEntry_ne_zero t u).1 hn)
  rw [← Finset.sum_subset (Finset.subset_univ ({t, t.swap} : Finset (A × A)))
    (fun u _ hu => by rw [hsupport u hu, zero_mul])]
  by_cases hd : t.swap = t
  · have hdiag : t.1 = t.2 := (congrArg Prod.snd hd)
    simp only [hd]
    by_cases hs : t = s
    · subst s
      simp [pairSize, swapEntry, hdiag]
    · have hn : ¬samePair t s := by
        rintro (h | h)
        · exact hs h
        · apply hs
          have he : s.swap = s := by simpa [h] using hd.symm
          exact h.trans he
      have hz : swapEntry s t = 0 := not_ne_iff.mp (mt (swapEntry_ne_zero s t).1 hn)
      simp [hz, hs]
  · have hnd : t.1 ≠ t.2 := fun he => hd (Prod.ext he.symm he)
    have hn' : t ≠ t.swap := Ne.symm hd
    rw [Finset.sum_insert (by simpa using hn'), Finset.sum_singleton]
    by_cases hs : t = s
    · subst s
      simp [swapEntry, pairSize, hd, hnd]
      split_ifs <;> norm_num
    by_cases hb : t.swap = s
    · subst s
      simp only [swapEntry, hs, if_false, if_true, Prod.swap_swap, hd,
        Prod.fst_swap, Prod.snd_swap]
      rcases lt_or_gt_of_ne hnd with hl | hl
      · simp [hl.le, not_le_of_gt hl]
      · simp [hl.le, not_le_of_gt hl]
    · have hz : swapEntry s t = 0 := by
        unfold swapEntry
        have he : t ≠ s.swap := fun h => hb (by rw [h, Prod.swap_swap])
        simp [hs, he]
      have hw : swapEntry s t.swap = 0 := by
        unfold swapEntry
        have he : t.swap ≠ s.swap := fun h => hs (by simpa using congrArg Prod.swap h)
        simp [hb, he]
      simp [hz, hw, hs]

def weight (t : WordCell I A) : ℕ := (Finset.univ.filter fun i => (t i).2 < (t i).1).card

def unequal (t : WordCell I A) : Finset I := Finset.univ.filter fun i => (t i).1 ≠ (t i).2

def walsh (t u : WordCell I A) : ℚ := ∏ i, swapEntry (t i) (u i)

def energy (t : WordCell I A) : ℚ := ∏ i, pairSize (t i)

lemma walsh_ne_zero (t u : WordCell I A) :
    walsh t u ≠ 0 ↔ ∀ i, samePair (u i) (t i) := by
  simp [walsh, Finset.prod_ne_zero_iff, swapEntry_ne_zero]

lemma energy_pos (t : WordCell I A) : 0 < energy t := by
  apply Finset.prod_pos
  intro i _
  unfold pairSize
  split_ifs <;> norm_num

lemma energy_eq (t : WordCell I A) : energy t = 2 ^ (unequal t).card := by
  unfold energy unequal
  rw [← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all [pairSize]

lemma gram_walsh (t s : WordCell I A) :
    ∑ u, walsh t u * walsh s u = if t = s then energy t else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (z : A × A) => swapEntry (t i) z * swapEntry (s i) z)]
  simp_rw [gram_swapEntry]
  by_cases h : t = s
  · subst s
    simp [energy]
  · have hx : ∃ i, t i ≠ s i := by
      simpa only [funext_iff, not_forall] using h
    obtain ⟨i, hi⟩ := hx
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma samePair_unequal {u t : A × A} (h : samePair u t) :
    (u.1 ≠ u.2) ↔ (t.1 ≠ t.2) := by
  rcases h with h | h <;> subst u <;> simp [ne_comm]

lemma walsh_sq_of_support {t u : WordCell I A} (h : ∀ i, samePair (u i) (t i)) :
    walsh t u ^ 2 = 1 := by
  rw [walsh, ← Finset.prod_pow]
  simp [swapEntry_sq, h]

/-- Fixing the first word separates the positions in any one swap orbit. -/
lemma cell_eq_of_first_of_samePair {u v : WordCell I A}
    (h₁ : ∀ i, (u i).1 = (v i).1) (h₂ : ∀ i, samePair (u i) (v i)) : u = v := by
  funext i
  rcases h₂ i with h | h
  · exact h
  · have he : (v i).2 = (v i).1 := by simpa [h] using h₁ i
    exact h.trans (Prod.ext he he.symm)

#print axioms gram_walsh
#print axioms walsh_sq_of_support
#print axioms cell_eq_of_first_of_samePair

end Section6




