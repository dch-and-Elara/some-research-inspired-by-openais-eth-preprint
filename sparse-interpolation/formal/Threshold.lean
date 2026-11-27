import RationalTransfer

open Matrix GrenetMcCoy Round4Transfer

namespace GrenetRational

/-- Number of strictly negative indices in the infinite normalized grid. -/
def negativeLength (z : ℚ) : ℕ := (⌈-z⌉ : ℤ).toNat

/-- The first index whose normalized node is strictly positive. -/
def firstPositive (z : ℚ) : ℕ := (⌊-z⌋ + 1 : ℤ).toNat

theorem node_neg_iff (z : ℚ) (i : ℕ) :
    normalizedNode z i < 0 ↔ i < negativeLength z := by
  have h : normalizedNode z i < 0 ↔ (((i : ℤ) : ℚ) < -z) := by
    simp only [Int.cast_natCast, normalizedNode]
    constructor <;> intro h <;> linarith
  rw [h, ← Int.lt_ceil]
  unfold negativeLength
  omega

theorem node_pos_iff (z : ℚ) (i : ℕ) :
    0 < normalizedNode z i ↔ firstPositive z ≤ i := by
  have h : 0 < normalizedNode z i ↔ -z < ((i : ℤ) : ℚ) := by
    simp only [Int.cast_natCast, normalizedNode]
    constructor <;> intro h <;> linarith
  rw [h, ← Int.floor_lt]
  unfold firstPositive
  omega

def signThreshold (z : ℚ) (k : ℕ) : ℕ :=
  if k ≤ negativeLength z then k else firstPositive z + k

/-- The closed form in the manuscript, in terms of the reduced denominator. -/
def threshold (z : ℚ) (t : ℕ) : ℕ :=
  if 2 < z.den then 2*t else signThreshold z (2*t)

theorem signThreshold_le_iff (z : ℚ) (k m : ℕ) :
    signThreshold z k ≤ m ↔
      (k ≤ m ∧ k ≤ negativeLength z) ∨ firstPositive z + k ≤ m := by
  unfold signThreshold
  split <;> omega

theorem normalizedPrefix_mono {z : ℚ} {t m n : ℕ} (hmn : m ≤ n)
    (h : DeterminesUnboundedSparse (normalizedPrefix z m) t) :
    DeterminesUnboundedSparse (normalizedPrefix z n) t := by
  intro f g hf hg he
  exact h f g hf hg fun i => he (Fin.castLE hmn i)

theorem determines_at_signThreshold {z : ℚ} {t m : ℕ}
    (hm : signThreshold z (2*t) ≤ m) : DeterminesUnboundedSparse (normalizedPrefix z m) t := by
  rcases (signThreshold_le_iff z (2*t) m).mp hm with ⟨hm, hneg⟩ | hpos
  · let rows (i : Fin (2*t)) : Fin m := Fin.castLE hm i
    apply GrenetPaper.rational_determining_of_same_sign _ t rows
    · intro i j h
      have h₁ : (i.val : ℚ) = j.val := add_left_cancel h
      exact Fin.ext (Nat.cast_injective h₁)
    · exact Or.inr (fun i => (node_neg_iff z i.val).mpr (i.isLt.trans_le hneg))
  · let rows (i : Fin (2*t)) : Fin m := ⟨firstPositive z + i.val, by have := i.isLt; omega⟩
    apply GrenetPaper.rational_determining_of_same_sign _ t rows
    · intro i j h
      have h₁ : ((firstPositive z + i.val : ℕ) : ℚ) = (firstPositive z + j.val : ℕ) :=
        add_left_cancel h
      exact Fin.ext (Nat.add_left_cancel (Nat.cast_injective h₁))
    · exact Or.inl (fun i => (node_pos_iff z _).mpr (Nat.le_add_right ..))

theorem normalized_prefix_basic_lower {z : ℚ} {t m : ℕ} (hm : m < 2*t) :
    ¬ DeterminesUnboundedSparse (normalizedPrefix z m) t := by
  have he :
      progression (fun i : Fin m => i.val) z 1 = normalizedPrefix z m := by
    funext i
    simp [progression, normalizedPrefix, normalizedNode]
  rw [← he]
  exact GrenetPaper.rational_prefix_lt_two_t z 1 m t hm

/-- Interface for the strict branch. Its conclusion is about one square
evaluation matrix, indexed by arbitrary distinct exponents. -/
def StrictSquareStatement : Prop :=
  ∀ (z : ℚ), 2 < z.den → ∀ (n : ℕ) (e : Fin n → ℕ), Function.Injective e →
    (Matrix.of (fun i j : Fin n => (normalizedNode z i.val)^(e j))).det ≠ 0

/-- Closing the strict determinant lemma yields sufficiency at every length
at least 2t. Smaller supports use the initial rows of their own size. -/
theorem determines_of_strict_square (h : StrictSquareStatement) {z : ℚ}
    (hz : 2 < z.den) (t m : ℕ) (hm : 2*t ≤ m) :
    DeterminesUnboundedSparse (normalizedPrefix z m) t := by
  classical
  apply (determines_iff_supports _ _).mpr
  intro E hc
  let en : E ≃ Fin E.card := E.equivFinOfCardEq rfl
  let e (j : Fin E.card) := (en.symm j).val
  let rows (a : E) : Fin m := Fin.castLE (hc.trans hm) (en a)
  let M := (evaluationMatrix (normalizedPrefix z m) E).submatrix rows id
  have hh := h z hz E.card e (Subtype.val_injective.comp en.symm.injective)
  have hd : M.det ≠ 0 := by
    rw [← Matrix.det_submatrix_equiv_self en.symm M]
    convert hh using 2
    ext i j
    change (normalizedNode z (en (en.symm i)).val)^e j = _
    rw [en.apply_symm_apply]
    rfl
  apply injective_of_fullMinorIdeal_eq_top
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨rows, rfl⟩)
    (isUnit_iff_ne_zero.mpr hd)

/-- Interface for the half-grid branch. The statement supplies only the
short-prefix obstruction, with no sufficiency assumption. -/
def HalfObstructionStatement : Prop :=
  ∀ (z : ℚ), z.den ≤ 2 → ∀ (t m : ℕ), 1 ≤ t → m < signThreshold z (2*t) →
    ¬ DeterminesUnboundedSparse (normalizedPrefix z m) t

theorem normalized_prefix_iff_of_branches
    (strict : StrictSquareStatement) (half : HalfObstructionStatement)
    (z : ℚ) (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (normalizedPrefix z m) t ↔ threshold z t ≤ m := by
  by_cases hz : 2 < z.den
  · rw [threshold, if_pos hz]
    refine ⟨fun h => ?_, determines_of_strict_square strict hz t m⟩
    by_contra! hc
    exact normalized_prefix_basic_lower hc h
  · rw [threshold, if_neg hz]
    refine ⟨fun h => ?_, determines_at_signThreshold⟩
    by_contra! hc
    exact half z (Nat.le_of_not_gt hz) t m ht hc h

theorem rational_ratio_exact_of_branches {R : Type*} [CommRing R] [Nontrivial R]
    [IsAddTorsionFree R] (strict : StrictSquareStatement) (half : HalfObstructionStatement)
    (a b : R) (A : ℤ) (B : ℕ) (hB : 0 < B) (hb : b ∈ nonZeroDivisors R)
    (hRatio : (B : R)*a = (A : R)*b) (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (ringPrefix a b m) t ↔ threshold (A / (B : ℚ)) t ≤ m :=
  (rational_ratio_prefix_iff a b A B (Nat.ne_of_gt hB) hb hRatio t m).trans
    (normalized_prefix_iff_of_branches strict half _ t m ht)

end GrenetRational
