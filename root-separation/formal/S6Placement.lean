import S6Orbit
import S6Trace

namespace Section6

open Finset
open scoped BigOperators RealInnerProductSpace
set_option linter.unusedSectionVars false

noncomputable section

variable {V H I A : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A]

/-- An injectively occupied array. Each occupied slot is exactly one incidence.
Several slots may point to the same original variable. -/
structure Placement (V H I A : Type*) where
  owner : H × WordCell I A → Option V
  first : V → I → A
  occurs : ∀ v, ∃ x, owner x = some v
  compatible : ∀ x v, owner x = some v → ∀ i, (x.2 i).1 = first v i

abbrev Exceptional (I A : Type*) [Fintype I] [LinearOrder A] (window : Finset ℕ) :=
  {t : WordCell I A // weight t ∉ window}

def blockWalsh (h : H) (t : WordCell I A) (x : H × WordCell I A) : ℚ :=
  if x.1 = h then walsh t x.2 else 0

def occurrences (P : Placement V H I A) (v : V) : Finset (H × WordCell I A) :=
  univ.filter fun x => P.owner x = some v

def incidenceEntry (P : Placement V H I A) (v : V) (x : H × WordCell I A) : ℚ :=
  if P.owner x = some v then 1 else 0

/-- This is the rational matrix C̃ ι. Each row uses exactly one copy of the
exceptional tensor measurement, and the column sum inserts the incidence values. -/
def actualMatrix (P : Placement V H I A) (window : Finset ℕ) :
    Matrix (H × Exceptional I A window) V ℚ :=
  fun a v => ∑ x ∈ occurrences P v, blockWalsh a.1 a.2.val x

def actualSummary (P : Placement V H I A) (window : Finset ℕ) (i : I) (x : V → Bool) :
    A → (H × Exceptional I A window) → ℚ :=
  fun g => (actualMatrix P window).mulVec (fun v =>
    if P.first v i = g then BooleanMeasurement.bit ℚ (x v) else 0)

lemma block_gram (h k : H) (t s : WordCell I A) :
    ∑ x, blockWalsh h t x * blockWalsh k s x =
      if (h, t) = (k, s) then energy t else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  by_cases he : h = k
  · subst k
    simp only [blockWalsh, ite_mul, mul_ite, mul_zero, zero_mul]
    simp [gram_walsh]
  · have hz (c : H) : ∀ u : WordCell I A, blockWalsh h t (c, u) * blockWalsh k s (c, u) = 0 := by
      intro u
      by_cases hc : c = h
      · subst c
        simp [blockWalsh, he]
      · simp [blockWalsh, hc]
    simp [hz, he]

lemma incidence_gram (P : Placement V H I A) (v w : V) :
    ∑ x, incidenceEntry P v x * incidenceEntry P w x =
      if v = w then ((occurrences P v).card : ℚ) else 0 := by
  classical
  by_cases hvw : v = w
  · subst w
    rw [if_pos rfl, card_eq_sum_ones, Nat.cast_sum, occurrences, sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : P.owner x = some v <;> simp [incidenceEntry, hx]
  · rw [if_neg hvw]
    apply sum_eq_zero
    intro x _
    by_cases hx : P.owner x = some v
    · simp [incidenceEntry, hx, hvw]
    · simp [incidenceEntry, hx]

lemma normalize_gram {X J : Type*} [Fintype X] [Fintype J]
    (v : J → X → ℚ) (e : J → ℚ) (he : ∀ j, 0 < e j) [DecidableEq J]
    (h : ∀ i j, ∑ x, v i x * v j x = if i = j then e i else 0) :
    Orthonormal ℝ (fun j => (WithLp.toLp 2 (fun x =>
      (Real.sqrt (e j : ℝ))⁻¹ * (v j x : ℝ)) : Euc X)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have hs (i : J) : Real.sqrt (e i : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast he i)).ne'
  rw [euclidean_inner]
  change (∑ x, ((√(↑(e i) : ℝ))⁻¹ * (v i x : ℝ)) *
      ((√(↑(e j) : ℝ))⁻¹ * (v j x : ℝ))) = _
  calc
    _ = (√(↑(e i) : ℝ))⁻¹ * (√(↑(e j) : ℝ))⁻¹ *
        ((∑ x, v i x * v j x : ℚ) : ℝ) := by
      push_cast
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [h]
      split_ifs with hij
      · subst j
        field_simp [hs i]
        nlinarith [Real.sq_sqrt (show 0 ≤ (e i : ℝ) by exact_mod_cast (he i).le)]
      · simp

lemma block_support_unique (P : Placement V H I A) (v : V) (a : H) (t : WordCell I A)
    {x y : H × WordCell I A} (hx : x ∈ occurrences P v) (hy : y ∈ occurrences P v)
    (hx' : blockWalsh a t x ≠ 0) (hy' : blockWalsh a t y ≠ 0) : x = y := by
  have hc (z : H × WordCell I A) (hz : blockWalsh a t z ≠ 0) :
      z.1 = a ∧ ∀ i, samePair (z.2 i) (t i) := by
    by_cases h : z.1 = a
    · exact ⟨h, (walsh_ne_zero t z.2).mp (by simpa [blockWalsh, h] using hz)⟩
    · exact False.elim (hz (by simp [blockWalsh, h]))
  obtain ⟨cx, hxo⟩ := hc x hx'
  obtain ⟨cy, hyo⟩ := hc y hy'
  have hfirst (z : H × WordCell I A) (hz : z ∈ occurrences P v) (i : I) :
      (z.2 i).1 = P.first v i := P.compatible z v (by simpa [occurrences] using hz) i
  exact Prod.ext (cx.trans cy.symm) (cell_eq_of_first_of_samePair
    (fun i => (hfirst x hx i).trans (hfirst y hy i).symm)
    (fun i => samePair_trans (hxo i) (samePair_symm (hyo i))))

lemma actualEntry_sq (P : Placement V H I A) (window : Finset ℕ)
    (a : H × Exceptional I A window) (v : V) :
    actualMatrix P window a v ^ 2 =
      ∑ x ∈ occurrences P v, blockWalsh a.1 a.2.val x ^ 2 := by
  classical
  by_cases hh : ∃ x ∈ occurrences P v, blockWalsh a.1 a.2.val x ≠ 0
  · obtain ⟨x, hx, hn⟩ := hh
    unfold actualMatrix
    rw [sum_eq_single_of_mem x hx (fun y hy hne => by
      by_contra h
      exact hne (block_support_unique P v a.1 a.2.val hy hx h hn))]
    rw [sum_eq_single_of_mem x hx (fun y hy hne => by
      have hz : blockWalsh a.1 a.2.val y = 0 := by
        by_contra h
        exact hne (block_support_unique P v a.1 a.2.val hy hx h hn)
      simp [hz])]
  · push_neg at hh
    have hz : actualMatrix P window a v = 0 := sum_eq_zero hh
    rw [hz, zero_pow (by decide : 2 ≠ 0)]
    exact (sum_eq_zero (fun x hx => by simp [hh x hx])).symm

lemma scaled_inner (P : Placement V H I A) (window : Finset ℕ) (a : H × Exceptional I A window) (v : V) :
    ⟪(WithLp.toLp 2 (fun x => (√(↑(energy a.2.val) : ℝ))⁻¹ *
        (blockWalsh a.1 a.2.val x : ℝ)) : Euc (H × WordCell I A)),
      (WithLp.toLp 2 (fun x => (√((occurrences P v).card : ℝ))⁻¹ *
        (incidenceEntry P v x : ℝ)) : Euc (H × WordCell I A))⟫ =
    (√((occurrences P v).card : ℝ))⁻¹ *
      ((√(↑(energy a.2.val) : ℝ))⁻¹ * (actualMatrix P window a v : ℝ)) := by
  classical
  rw [euclidean_inner]
  unfold actualMatrix occurrences
  push_cast
  rw [sum_filter, mul_sum, mul_sum]
  apply sum_congr rfl
  intro x _
  change _ = _
  by_cases hx : P.owner x = some v <;> simp [incidenceEntry, hx] <;> ring

/-- The projection trace lower bound for the actual rational measurement matrix. -/
theorem projection_trace_rank (P : Placement V H I A) (window : Finset ℕ) :
    ∑ v, (∑ x ∈ occurrences P v, fairTail (unequal x.2).card window) /
          ((occurrences P v).card : ℚ) ≤ (actualMatrix P window).rank := by
  classical
  have hp (v : V) : 0 < (occurrences P v).card := by
    obtain ⟨x, hx⟩ := P.occurs v
    exact card_pos.mpr ⟨x, by simp [occurrences, hx]⟩
  let rowScale (a : H × Exceptional I A window) := (√(↑(energy a.2.val) : ℝ))⁻¹
  let colScale (v : V) := (√((occurrences P v).card : ℝ))⁻¹
  have hr := normalize_gram
    (fun (a : H × Exceptional I A window) => blockWalsh a.1 a.2.val)
    (fun a => energy a.2.val) (fun a => energy_pos a.2.val)
    (fun a b => by
      simpa only [Prod.mk.injEq, Prod.ext_iff, Subtype.coe_inj] using block_gram a.1 b.1 a.2.val b.2.val)
  have hi := normalize_gram (incidenceEntry P) (fun v => ((occurrences P v).card : ℚ))
    (fun v => by dsimp; exact_mod_cast hp v) (incidence_gram P)
  let r (a : H × Exceptional I A window) : Euc (H × WordCell I A) :=
    WithLp.toLp 2 (fun x => rowScale a * (blockWalsh a.1 a.2.val x : ℝ))
  let e (v : V) : Euc (H × WordCell I A) :=
    WithLp.toLp 2 (fun x => colScale v * (incidenceEntry P v x : ℝ))
  change Orthonormal ℝ r at hr
  have he : Orthonormal ℝ e := by
    simpa only [Rat.cast_natCast] using hi
  have hco (v : V) (a : H × Exceptional I A window) :
      ⟪r a, e v⟫ = colScale v * (rowScale a * (actualMatrix P window a v : ℝ)) :=
    scaled_inner P window a v
  have htrace := trace_le_measured_dim r e hr he
  have hcols :
      (fun v => (WithLp.toLp 2 (fun a => ⟪r a, e v⟫) : Euc (H × Exceptional I A window))) =
      (fun v => WithLp.toLp 2 (fun a => colScale v * (rowScale a * (actualMatrix P window a v : ℝ)))) := by
    funext v
    exact congrArg (WithLp.toLp 2) (funext (hco v))
  rw [hcols] at htrace
  simp_rw [hco] at htrace
  have hdim := scaled_real_span_le_rat_rank (actualMatrix P window) rowScale colScale
  have hle := htrace.trans (by exact_mod_cast hdim : (_ : ℝ) ≤ (actualMatrix P window).rank)
  have hscale (v : V) (a : H × Exceptional I A window) :
      (colScale v * (rowScale a * (actualMatrix P window a v : ℝ))) ^ 2 =
      (((actualMatrix P window a v ^ 2 / energy a.2.val) /
          ((occurrences P v).card : ℚ) : ℚ) : ℝ) := by
    unfold rowScale colScale
    have h₁ : (0 : ℝ) ≤ (energy a.2.val : ℝ) := by exact_mod_cast (energy_pos a.2.val).le
    push_cast
    have h₂ : (0 : ℝ) ≤ ((occurrences P v).card : ℝ) := by positivity
    simp only [mul_pow, inv_pow, Real.sq_sqrt h₂, Real.sq_sqrt h₁]
    ring
  simp_rw [hscale] at hle
  have hsum (v : V) : ∑ a : H × Exceptional I A window,
      actualMatrix P window a v ^ 2 / energy a.2.val =
      ∑ x ∈ occurrences P v, fairTail (unequal x.2).card window := by
    simp_rw [actualEntry_sq, sum_div]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [Fintype.sum_prod_type]
    simp only [blockWalsh, ite_pow, zero_pow (by decide : 2 ≠ 0), ite_div, zero_div,
      sum_ite_irrel, sum_const_zero, Finset.sum_ite_eq, mem_univ, if_true]
    exact projection_diagonal x.2 window
  simp_rw [← hsum, sum_div]
  exact_mod_cast hle

/-- F.A1, with the first logarithm expressed as the equivalent cardinal bound. -/
theorem FA1 (P : Placement V H I A) (window : Finset ℕ) (i : I) :
    (∑ v, (∑ x ∈ occurrences P v, fairTail (unequal x.2).card window) /
          ((occurrences P v).card : ℚ) ≤ (actualMatrix P window).rank) ∧
    2 ^ (actualMatrix P window).rank ≤ (Set.range (actualSummary P window i)).ncard := by
  exact ⟨projection_trace_rank P window,
    BooleanMeasurement.two_pow_rank_le_grouped_range_ncard
      (actualMatrix P window) (fun v => P.first v i)⟩

#print axioms normalize_gram
#print axioms block_support_unique
#print axioms actualEntry_sq
#print axioms projection_trace_rank
#print axioms FA1

end
end Section6






