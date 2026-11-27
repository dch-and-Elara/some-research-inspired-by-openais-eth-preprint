import RationalSign

open Polynomial GrenetMcCoy Round4Transfer

namespace GrenetHalf

/-- Indices of the strictly positive and strictly negative samples. -/
def posIndices {ι : Type*} [Fintype ι] (x : ι → ℚ) : Finset ι :=
  Finset.univ.filter fun i => 0 < x i

def negIndices {ι : Type*} [Fintype ι] (x : ι → ℚ) : Finset ι :=
  Finset.univ.filter fun i => x i < 0

/-- Absolute values of the nonzero samples, with duplicates removed. -/
def nonzeroAbs {ι : Type*} [Fintype ι] (x : ι → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => x i ≠ 0).image fun i => |x i|

/-- The doubled normalized grid at a half-integral start. -/
def doubleNode {m : ℕ} (c : ℤ) (i : Fin m) : ℤ :=
  c + 2 * (i.val : ℤ)

private theorem reflect_index {m : ℕ} (c : ℤ) (i : Fin m)
    (hl : 0 ≤ -c - i.val) (hu : -c - (i.val : ℤ) < m) :
    ∃ j : Fin m, doubleNode c j = -doubleNode c i := by
  let j : Fin m := ⟨(-c - (i.val : ℤ)).toNat, by omega⟩
  have hj : (j.val : ℤ) = -c - i.val := by
    exact Int.toNat_of_nonneg hl
  exact ⟨j, by unfold doubleNode; rw [hj]; omega⟩

/-- One whole sign class of a half-integral prefix has its opposite in the prefix.
The integer reflection index is -c-i, and the empty prefix is allowed. -/
theorem doubleNode_reflect_side (c : ℤ) (m : ℕ) :
    (∀ i : Fin m, 0 < doubleNode c i → ∃ j : Fin m, doubleNode c j = -doubleNode c i) ∨
    (∀ i : Fin m, doubleNode c i < 0 → ∃ j : Fin m, doubleNode c j = -doubleNode c i) := by
  by_cases h : c + (m : ℤ) < 1
  · left
    intro i hi
    have hb := i.isLt
    unfold doubleNode at hi
    exact reflect_index c i (by omega) (by omega)
  · right
    intro i hi
    unfold doubleNode at hi
    exact reflect_index c i (by omega) (by omega)

section Counts

variable {ι : Type*} [Fintype ι]

private def posAbs (x : ι → ℚ) : Finset ℚ := (posIndices x).image fun i => |x i|
private def negAbs (x : ι → ℚ) : Finset ℚ := (negIndices x).image fun i => |x i|

private theorem nonzeroAbs_union (x : ι → ℚ) :
    nonzeroAbs x = posAbs x ∪ negAbs x := by
  classical
  unfold nonzeroAbs posAbs negAbs
  rw [← Finset.image_union]
  congr 1
  ext i
  simp only [posIndices, negIndices, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h =>
    h.elim (fun hn => ne_of_gt hn) (fun hn => ne_of_lt hn)⟩

private theorem posAbs_card (x : ι → ℚ) (hx : Function.Injective x) :
    (posAbs x).card = (posIndices x).card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj h
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hx (by simpa only [abs_of_pos hi', abs_of_pos hj'] using h)

private theorem negAbs_card (x : ι → ℚ) (hx : Function.Injective x) :
    (negAbs x).card = (negIndices x).card := by
  apply Finset.card_image_of_injOn
  intro i hi j hj h
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  exact hx (neg_injective (by simpa only [abs_of_neg hi', abs_of_neg hj'] using h))

/-- If all samples on one side are paired with opposites, the two magnitude sets
are nested. Their union has the larger of the two sign counts. -/
theorem card_nonzeroAbs_of_reflect_side (x : ι → ℚ) (hx : Function.Injective x)
    (h : (∀ i, 0 < x i → ∃ j, x j = -x i) ∨
         (∀ i, x i < 0 → ∃ j, x j = -x i)) :
    (nonzeroAbs x).card = max (posIndices x).card (negIndices x).card := by
  rcases h with h | h
  · have hsub : posAbs x ⊆ negAbs x := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi' := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj⟩ := h i hi'
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj]; exact neg_neg_of_pos hi'⟩,
        by rw [hj, abs_neg]⟩
    have hc := Finset.card_le_card hsub
    rw [posAbs_card x hx, negAbs_card x hx] at hc
    rw [nonzeroAbs_union, Finset.union_eq_right.mpr hsub, negAbs_card x hx, max_eq_right hc]
  · have hsub : negAbs x ⊆ posAbs x := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi' := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj⟩ := h i hi'
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hj]; exact neg_pos.mpr hi'⟩,
        by rw [hj, abs_neg]⟩
    have hc := Finset.card_le_card hsub
    rw [posAbs_card x hx, negAbs_card x hx] at hc
    rw [nonzeroAbs_union, Finset.union_eq_left.mpr hsub, posAbs_card x hx, max_eq_left hc]

/-- At most t terms are determined exactly when one sign reaches 2t, for
an injective list whose smaller magnitude set is covered by opposite samples. -/
theorem rational_determining_iff_of_reflect_side (x : ι → ℚ)
    (hx : Function.Injective x)
    (hm : (∀ i, 0 < x i → ∃ j, x j = -x i) ∨
          (∀ i, x i < 0 → ∃ j, x j = -x i)) (t : ℕ) :
    DeterminesUnboundedSparse x t ↔ 2*t ≤ max (posIndices x).card (negIndices x).card := by
  classical
  constructor
  · intro h
    by_contra! ht
    let s := (nonzeroAbs x).image (fun a => a^2)
    have hs : s.card < 2*t := by
      exact Finset.card_image_le.trans_lt (by rwa [card_nonzeroAbs_of_reflect_side x hx hm])
    refine GrenetPaper.not_determining_of_small_squared_sample_set x t s hs ?_ h
    intro i
    by_cases hi : x i = 0
    · exact Or.inl hi
    · right
      exact Finset.mem_image.mpr ⟨|x i|, Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩, sq_abs _⟩
  · intro h
    rcases le_max_iff.mp h with hp | hn
    · obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin (2*t)) (by simpa using hp)
      exact GrenetPaper.rational_determining_of_same_sign x t f (hx.comp f.injective)
        (Or.inl fun i => (Finset.mem_filter.mp (hf (Set.mem_range_self i))).2)
    · obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin (2*t)) (by simpa using hn)
      exact GrenetPaper.rational_determining_of_same_sign x t f (hx.comp f.injective)
        (Or.inr fun i => (Finset.mem_filter.mp (hf (Set.mem_range_self i))).2)

end Counts

/-- The reflection survives positive or negative scaling. -/
theorem progression_reflect_side (a b : ℚ) (hb : b ≠ 0) (c : ℤ)
    (hc : 2 * (a/b) = (c : ℚ)) (m : ℕ) :
    let x := progression (fun i : Fin m => i.val) a b
    (∀ i, 0 < x i → ∃ j, x j = -x i) ∨ (∀ i, x i < 0 → ∃ j, x j = -x i) := by
  let x := progression (fun i : Fin m => i.val) a b
  have hmul := congrArg (fun z : ℚ => z*b) hc
  change (2 * (a/b))*b = (c : ℚ)*b at hmul
  rw [mul_assoc 2, div_mul_cancel₀ _ hb] at hmul
  have hpoint (i : Fin m) : x i = (doubleNode c i : ℚ) * (b/2) := by
    have ha : a = (c : ℚ)*(b/2) := by linarith
    simp only [x, progression, doubleNode, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, ha]
    ring
  have pair (i j : Fin m) (h : doubleNode c j = -doubleNode c i) : x j = -x i := by
    rw [hpoint j, hpoint i, h, Int.cast_neg, neg_mul]
  rcases doubleNode_reflect_side c m with h | h
  · rcases lt_or_gt_of_ne hb with hb | hb
    · right
      intro i hi
      change x i < 0 at hi
      rw [hpoint] at hi
      have hs := (mul_neg_iff.mp hi).resolve_right
        (fun hh => (by linarith [hh.2] : False))
      obtain ⟨j, hj⟩ := h i (by exact_mod_cast hs.1)
      exact ⟨j, pair i j hj⟩
    · left
      intro i hi
      change 0 < x i at hi
      rw [hpoint] at hi
      have hs := (mul_pos_iff.mp hi).resolve_right
        (fun hh => (by linarith [hh.2] : False))
      obtain ⟨j, hj⟩ := h i (by exact_mod_cast hs.1)
      exact ⟨j, pair i j hj⟩
  · rcases lt_or_gt_of_ne hb with hb | hb
    · left
      intro i hi
      change 0 < x i at hi
      rw [hpoint] at hi
      have hs := (mul_pos_iff.mp hi).resolve_left
        (fun hh => (by linarith [hh.2] : False))
      obtain ⟨j, hj⟩ := h i (by exact_mod_cast hs.1)
      exact ⟨j, pair i j hj⟩
    · right
      intro i hi
      change x i < 0 at hi
      rw [hpoint] at hi
      have hs := (mul_neg_iff.mp hi).resolve_left
        (fun hh => (by linarith [hh.2] : False))
      obtain ⟨j, hj⟩ := h i (by exact_mod_cast hs.1)
      exact ⟨j, pair i j hj⟩

private theorem progression_injective_rat (a b : ℚ) (hb : b ≠ 0) (m : ℕ) :
    Function.Injective (progression (fun i : Fin m => i.val) a b) := by
  intro i j h
  exact Fin.ext (Nat.cast_injective (mul_right_cancel₀ hb (add_left_cancel h)))

/-- Count of distinct nonzero magnitudes in a signed half-integral progression. -/
theorem rational_progression_card_nonzeroAbs (a b : ℚ) (hb : b ≠ 0) (c : ℤ)
    (hc : 2 * (a/b) = (c : ℚ)) (m : ℕ) :
    let x := progression (fun i : Fin m => i.val) a b
    (nonzeroAbs x).card = max (posIndices x).card (negIndices x).card :=
  card_nonzeroAbs_of_reflect_side _ (progression_injective_rat a b hb m)
    (progression_reflect_side a b hb c hc m)

/-- The half-integral/integer branch of the rational prefix classification,
for all prefixes and all t, also at a negative step. -/
theorem rational_half_prefix_iff (a b : ℚ) (hb : b ≠ 0) (c : ℤ)
    (hc : 2 * (a/b) = (c : ℚ)) (m t : ℕ) :
    let x := progression (fun i : Fin m => i.val) a b
    DeterminesUnboundedSparse x t ↔
      2*t ≤ (posIndices x).card ∨ 2*t ≤ (negIndices x).card :=
  (rational_determining_iff_of_reflect_side _ (progression_injective_rat a b hb m)
    (progression_reflect_side a b hb c hc m) t).trans le_max_iff

end GrenetHalf
