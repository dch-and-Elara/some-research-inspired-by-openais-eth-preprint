import SparseEvaluation
import Mathlib.Data.ZMod.Basic

open Polynomial Matrix

namespace GrenetMcCoy

variable {R ι : Type*} [CommRing R]

/-- The support lies strictly below d, including the empty support at d = 0. -/
def LowerSparse (d s : ℕ) (p : R[X]) : Prop :=
  p.support ⊆ Finset.range d ∧ p.support.card ≤ s

def Vanishes (x : ι → R) (p : R[X]) : Prop :=
  ∀ i, p.eval (x i) = 0

def DeterminesLower (x : ι → R) (d s : ℕ) : Prop :=
  ∀ f g : R[X], LowerSparse d s f → LowerSparse d s g →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

/-- The leading coefficient must belong to A. Polynomial.degree excludes
the zero polynomial even when d = 0. -/
def DeterminesExactDegreeWith (x : ι → R) (d t : ℕ) (A : Set R) : Prop :=
  ∀ f g : R[X], f.degree = d → g.degree = d →
    f.support.card ≤ t → g.support.card ≤ t →
    f.coeff d ∈ A → g.coeff d ∈ A →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

def DeterminesFixedLeading (x : ι → R) (d t : ℕ) (a : R) : Prop :=
  DeterminesExactDegreeWith x d t {a}

def DeterminesExactDegree (x : ι → R) (d t : ℕ) : Prop :=
  DeterminesExactDegreeWith x d t Set.univ

private theorem lowerSparse_zero_degree {s : ℕ} {p : R[X]}
    (hp : LowerSparse 0 s p) : p = 0 := by
  apply support_eq_empty.mp
  simpa using hp.1

private theorem lowerSparse_succ_iff (d s : ℕ) (p : R[X]) :
    LowerSparse (d + 1) s p ↔ Admissible d s p := by
  constructor
  · intro h
    refine ⟨natDegree_le_iff_coeff_eq_zero.mpr fun _ hi => notMem_support_iff.mp ?_, h.2⟩
    exact fun hm => (not_lt_of_ge (Nat.succ_le_of_lt hi)) (Finset.mem_range.mp (h.1 hm))
  · intro h
    exact ⟨supp_subset_range (Nat.lt_succ_of_le h.1), h.2⟩

theorem lowerSparse_iff_split (d s : ℕ) (p : R[X]) :
    LowerSparse d (2 * s) p ↔
      ∃ f g : R[X], LowerSparse d s f ∧ LowerSparse d s g ∧ p = f - g := by
  cases d with
  | zero =>
    constructor
    · intro hp
      rw [lowerSparse_zero_degree hp]
      exact ⟨0, 0, by simp [LowerSparse], by simp [LowerSparse], by simp⟩
    · rintro ⟨f, g, hf, hg, rfl⟩
      rw [lowerSparse_zero_degree hf, lowerSparse_zero_degree hg, sub_self]
      simp [LowerSparse]
  | succ d =>
    simp only [lowerSparse_succ_iff]
    exact admissible_iff_split p

private theorem determinesLower_iff_kernel (x : ι → R) (d s : ℕ) :
    DeterminesLower x d s ↔
      ∀ p : R[X], LowerSparse d (2 * s) p → Vanishes x p → p = 0 := by
  constructor
  · intro h p hp hz
    obtain ⟨f, g, hf, hg, rfl⟩ := (lowerSparse_iff_split d s p).mp hp
    rw [h f g hf hg (fun i => sub_eq_zero.mp (by simpa [eval_sub] using hz i)), sub_self]
  · intro h f g hf hg hsame
    apply sub_eq_zero.mp
    exact h _ ((lowerSparse_iff_split d s _).mpr ⟨f, g, hf, hg, rfl⟩)
      fun i => by rw [eval_sub, hsame i, sub_self]

private theorem coeff_top_zero {d : ℕ} {p : R[X]} (hp : p.support ⊆ Finset.range d) :
    p.coeff d = 0 :=
  notMem_support_iff.mp (fun h => (Nat.lt_irrefl d) (Finset.mem_range.mp (hp h)))

private theorem coeff_top_add {d : ℕ} {p : R[X]} (hp : p.support ⊆ Finset.range d) (a : R) :
    (monomial d a + p).coeff d = a := by
  rw [coeff_add, coeff_monomial_same, coeff_top_zero hp, add_zero]

private theorem support_top_add {d : ℕ} {p : R[X]} (hp : p.support ⊆ Finset.range d)
    {a : R} (ha : a ≠ 0) : (monomial d a + p).support = insert d p.support := by
  ext j
  by_cases hj : j = d
  · subst j
    simp [mem_support_iff, coeff_top_add hp a, ha]
  · rw [mem_support_iff, coeff_add, coeff_monomial_of_ne _ hj, zero_add]
    simp [hj, mem_support_iff]

private theorem degree_data {d : ℕ} {p : R[X]} (hp : p.degree = d) :
    p.natDegree = d ∧ p.coeff d ≠ 0 := by
  have hn := natDegree_eq_of_degree_eq_some hp
  have hne : p ≠ 0 := by intro hz; simp [hz] at hp
  exact ⟨hn, by rw [← hn, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hne⟩

private theorem erase_top_lower {d t : ℕ} {p : R[X]} (hd : p.degree = d)
    (ht : p.support.card ≤ t) : LowerSparse d (t - 1) (p.erase d) := by
  obtain ⟨hn, hc⟩ := degree_data hd
  have hcard := Finset.card_erase_add_one (mem_support_iff.mpr hc)
  unfold LowerSparse
  rw [support_erase]
  constructor
  · intro e he
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp he
    have hle := le_natDegree_of_ne_zero (mem_support_iff.mp hm)
    exact Finset.mem_range.mpr (by omega)
  · omega

private theorem exact_degree_top_add {d : ℕ} {p : R[X]} (hp : p.support ⊆ Finset.range d)
    {a : R} (ha : a ≠ 0) : (monomial d a + p).degree = d := by
  let q := monomial d a + p
  have hc : q.coeff d ≠ 0 := by rw [coeff_top_add hp]; exact ha
  have hn : q.natDegree ≤ d := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj => notMem_support_iff.mp ?_
    rw [support_top_add hp ha, Finset.mem_insert]
    rintro (he | he)
    · omega
    · exact (not_lt_of_ge hj.le) (Finset.mem_range.mp (hp he))
  have hz : q ≠ 0 := fun he => hc (by simp [he])
  rw [degree_eq_natDegree hz, natDegree_eq_of_le_of_coeff_ne_zero hn hc]

private theorem card_top_add {d : ℕ} {p : R[X]} (hp : p.support ⊆ Finset.range d)
    {a : R} (ha : a ≠ 0) : (monomial d a + p).support.card = p.support.card + 1 := by
  have hnot : d ∉ p.support := fun h => (Nat.lt_irrefl d) (Finset.mem_range.mp (hp h))
  rw [support_top_add hp ha, Finset.card_insert_of_notMem hnot]

private theorem top_sub (d : ℕ) (a b : R) (f g : R[X]) :
    (monomial d a + f) - (monomial d b + g) = monomial d (a - b) + (f - g) := by
  rw [map_sub]
  abel

/-- A common formulation: lower differences have ≤ 2(t-1) terms, while
the top coefficient ranges over differences of the allowed nonzero leaders. -/
theorem determinesExactDegreeWith_iff_difference_kernel (x : ι → R) (d t : ℕ)
    (A : Set R) (ht : 1 ≤ t) :
    DeterminesExactDegreeWith x d t A ↔
      ∀ a ∈ A, ∀ b ∈ A, a ≠ 0 → b ≠ 0 → ∀ p : R[X], LowerSparse d (2 * (t - 1)) p →
        Vanishes x (monomial d (a - b) + p) → monomial d (a - b) + p = 0 := by
  constructor
  · intro h a ha b hb hna hnb p hp hz
    obtain ⟨f, g, hf, hg, he⟩ := (lowerSparse_iff_split d (t - 1) p).mp hp
    have hdiff : (monomial d a + f) - (monomial d b + g) = monomial d (a - b) + p :=
      (top_sub d a b f g).trans (congrArg (monomial d (a - b) + ·) he.symm)
    have hfc : (monomial d a + f).support.card ≤ t := by
      rw [card_top_add hf.1 hna]
      have := hf.2
      omega
    have hgc : (monomial d b + g).support.card ≤ t := by
      rw [card_top_add hg.1 hnb]
      have := hg.2
      omega
    have hsame : ∀ i, (monomial d a + f).eval (x i) = (monomial d b + g).eval (x i) := by
      intro i
      apply sub_eq_zero.mp
      rw [← eval_sub, hdiff]
      exact hz i
    have heq := h _ _ (exact_degree_top_add hf.1 hna) (exact_degree_top_add hg.1 hnb)
      hfc hgc (by simpa [coeff_top_add hf.1] using ha) (by simpa [coeff_top_add hg.1] using hb) hsame
    rw [← hdiff, heq, sub_self]
  · intro h f g hf hg hfc hgc ha hb he
    have hdiff : f - g = monomial d (f.coeff d - g.coeff d) + (f.erase d - g.erase d) := by
      calc
        _ = (monomial d (f.coeff d) + f.erase d) - (monomial d (g.coeff d) + g.erase d) :=
          congrArg₂ (· - ·) (monomial_add_erase f d).symm (monomial_add_erase g d).symm
        _ = _ := top_sub _ _ _ _ _
    have hlower := (lowerSparse_iff_split d (t - 1) _).mpr
      ⟨_, _, erase_top_lower hf hfc, erase_top_lower hg hgc, rfl⟩
    apply sub_eq_zero.mp
    rw [hdiff]
    apply h _ ha _ hb (degree_data hf).2 (degree_data hg).2 _ hlower
    intro i
    rw [← hdiff, eval_sub, he, sub_self]

theorem determinesFixedLeading_iff_lower_kernel (x : ι → R) (d t : ℕ) (a : R)
    (ht : 1 ≤ t) (ha : a ≠ 0) :
    DeterminesFixedLeading x d t a ↔
      ∀ p : R[X], LowerSparse d (2 * (t - 1)) p → Vanishes x p → p = 0 := by
  rw [DeterminesFixedLeading, determinesExactDegreeWith_iff_difference_kernel _ _ _ _ ht]
  constructor
  · intro h p hp hz
    simpa using h a (Set.mem_singleton a) a (Set.mem_singleton a) ha ha p hp (by simpa)
  · intro h a' ha' b' hb' _ _ p hp hz
    rw [Set.mem_singleton_iff] at ha' hb'
    subst a'
    subst b'
    simpa using h p hp (by simpa using hz)

theorem determinesFixedLeading_iff_determinesLower (x : ι → R) (d t : ℕ) (a : R)
    (ht : 1 ≤ t) (ha : a ≠ 0) :
    DeterminesFixedLeading x d t a ↔ DeterminesLower x d (t - 1) :=
  (determinesFixedLeading_iff_lower_kernel x d t a ht ha).trans
    (determinesLower_iff_kernel x d (t - 1)).symm

/-- A ring with a third element has every element as a difference
of two nonzero elements. This hypothesis also allows infinite rings. -/
theorem exists_nonzero_sub_eq (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) (c : R) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a - b = c := by
  obtain ⟨u, hu0, hu1⟩ := third
  have hone : (1 : R) ≠ 0 := fun he => hu0 (by simpa [he] using (mul_one u).symm)
  by_cases hc : c + 1 = 0
  · refine ⟨c + u, u, ?_, hu0, add_sub_cancel_right _ _⟩
    intro h
    apply hu1
    calc
      u = (c + u) - c := by abel
      _ = (c + 1) - c := by rw [h, hc]
      _ = 1 := by abel
  · exact ⟨c + 1, 1, hc, hone, add_sub_cancel_right _ _⟩

theorem determinesExactDegree_iff_top_kernel (x : ι → R) (d t : ℕ) (ht : 1 ≤ t)
    (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) :
    DeterminesExactDegree x d t ↔
      ∀ (c : R) (p : R[X]), LowerSparse d (2 * (t - 1)) p →
        Vanishes x (monomial d c + p) → monomial d c + p = 0 := by
  rw [DeterminesExactDegree, determinesExactDegreeWith_iff_difference_kernel _ _ _ _ ht]
  constructor
  · intro h c p hp hz
    obtain ⟨a, b, ha, hb, he⟩ := exists_nonzero_sub_eq third c
    exact he ▸ h a (Set.mem_univ a) b (Set.mem_univ b) ha hb p hp (he.symm ▸ hz)
  · intro h a _ b _ _ _ p hp hz
    exact h (a - b) p hp hz

/-- The finite-cardinality way to supply a third element. -/
theorem exists_third_of_three_le_card [Fintype R] (h : 3 ≤ Fintype.card R) :
    ∃ u : R, u ≠ 0 ∧ u ≠ 1 := by
  classical
  have hsmall : ({0, 1} : Finset R).card ≤ 2 := by
    have hle := Finset.card_insert_le (0 : R) ({1} : Finset R)
    simpa using hle
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset R)) (t := Finset.univ) (by rw [Finset.card_univ]; omega)
  exact ⟨u, fun h => hu (by simp [h]), fun h => hu (by simp [h])⟩

private def NoKernelOn (x : ι → R) (E : Finset ℕ) : Prop :=
  ∀ p : R[X], p.support ⊆ E → Vanishes x p → p = 0

private theorem noKernelOn_iff_ideal (x : ι → R) (E : Finset ℕ) :
    NoKernelOn x E ↔ (fullMinorIdeal (evaluationMatrix x E)).annihilator = ⊥ := by
  rw [← determinesOn_iff_annihilator_eq_bot]
  constructor
  · intro h f g hf hg he
    apply sub_eq_zero.mp
    apply h _ ?_ (fun i => by rw [eval_sub, he, sub_self])
    intro j hj
    by_contra hn
    exact (mem_support_iff.mp hj) (by rw [coeff_sub,
      notMem_support_iff.mp (fun h => hn (hf h)),
      notMem_support_iff.mp (fun h => hn (hg h)), sub_self])
  · intro h p hp hz
    exact h p 0 hp (by simp) (fun i => by simpa using hz i)

private theorem lower_kernel_iff_support_tests (x : ι → R) (d k : ℕ) :
    (∀ p : R[X], LowerSparse d k p → Vanishes x p → p = 0) ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card ≤ k → NoKernelOn x E := by
  constructor
  · intro h E hE hcard p hp hz
    exact h p ⟨hp.trans hE, (Finset.card_le_card hp).trans hcard⟩ hz
  · intro h p hp hz
    exact h p.support hp.1 hp.2 p (Finset.Subset.refl _) hz

private theorem support_top_add_subset (d : ℕ) (c : R) (p : R[X]) :
    (monomial d c + p).support ⊆ insert d p.support := by
  intro j hj
  by_contra hn
  rw [Finset.mem_insert, not_or] at hn
  exact (mem_support_iff.mp hj) (by rw [coeff_add, coeff_monomial_of_ne _ hn.1,
    notMem_support_iff.mp hn.2, add_zero])

private theorem top_kernel_iff_support_tests (x : ι → R) (d k : ℕ) :
    (∀ (c : R) (p : R[X]), LowerSparse d k p →
      Vanishes x (monomial d c + p) → monomial d c + p = 0) ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card ≤ k → NoKernelOn x (insert d E) := by
  constructor
  · intro h E hE hcard q hq hz
    have hsub : (q.erase d).support ⊆ E := by
      rw [support_erase]
      intro j hj
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hj
      exact (Finset.mem_insert.mp (hq hm)).resolve_left hne
    have hl : LowerSparse d k (q.erase d) :=
      ⟨hsub.trans hE, (Finset.card_le_card hsub).trans hcard⟩
    simpa only [monomial_add_erase] using
      h (q.coeff d) (q.erase d) hl (by simpa only [monomial_add_erase])
  · intro h c p hp hz
    exact h p.support hp.1 hp.2 _ (support_top_add_subset d c p) hz

/-- The family of smaller support tests is equivalent to checking maximal
allowed supports. The mandatory columns in B are kept on both sides. -/
private theorem support_tests_iff_max_ideals (x : ι → R) (d k : ℕ)
    (columns : Finset ℕ → Finset ℕ) (hcolumns : Monotone columns) :
    (∀ E : Finset ℕ, E ⊆ Finset.range d → E.card ≤ k → NoKernelOn x (columns E)) ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card = min k d →
        (fullMinorIdeal (evaluationMatrix x (columns E))).annihilator = ⊥ := by
  simp_rw [← noKernelOn_iff_ideal]
  constructor
  · intro h E hE hc
    exact h E hE (hc ▸ min_le_left k d)
  · intro h E hE hc p hp hz
    have he : E.card ≤ min k d := le_min hc (by simpa using Finset.card_le_card hE)
    have hb : min k d ≤ (Finset.range d).card := by simp
    obtain ⟨T, hET, hT, hTc⟩ := Finset.exists_subsuperset_card_eq hE he hb
    exact h T hT hTc p (hp.trans (hcolumns hET)) hz

/-- Known nonzero leading coefficient: only the low columns are tested. -/
theorem determinesFixedLeading_iff_determinantal_annihilator (x : ι → R) (d t : ℕ) (a : R)
    (ht : 1 ≤ t) (ha : a ≠ 0) :
    DeterminesFixedLeading x d t a ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card = min (2 * (t - 1)) d →
        (fullMinorIdeal (evaluationMatrix x E)).annihilator = ⊥ := by
  rw [determinesFixedLeading_iff_lower_kernel x d t a ht ha, lower_kernel_iff_support_tests]
  exact support_tests_iff_max_ideals x d (2 * (t - 1)) id monotone_id

/-- Variable leading coefficient: adjoin the top column to each allowed
support of size at most 2(t-1) below d. -/
theorem determinesExactDegree_iff_support_matrices (x : ι → R) (d t : ℕ)
    (ht : 1 ≤ t) (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) :
    DeterminesExactDegree x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card ≤ 2 * (t - 1) →
        Function.Injective (evaluationMatrix x (insert d E)).mulVec := by
  rw [determinesExactDegree_iff_top_kernel x d t ht third, top_kernel_iff_support_tests]
  simp_rw [mulVec_injective_iff_fullMinorIdeal_annihilator_eq_bot, ← noKernelOn_iff_ideal]

/-- The equivalent maximal-size ideal criterion, with the top column
required in every test. -/
theorem determinesExactDegree_iff_determinantal_annihilator (x : ι → R) (d t : ℕ)
    (ht : 1 ≤ t) (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) :
    DeterminesExactDegree x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card = min (2 * (t - 1)) d →
        (fullMinorIdeal (evaluationMatrix x (insert d E))).annihilator = ⊥ := by
  rw [determinesExactDegree_iff_top_kernel x d t ht third, top_kernel_iff_support_tests]
  exact support_tests_iff_max_ideals x d (2 * (t - 1)) (insert d) (fun _ _ h =>
    Finset.insert_subset_insert d h)

theorem top_column_count {d t : ℕ} (ht : 1 ≤ t) {E : Finset ℕ}
    (hE : E ⊆ Finset.range d) (hcard : E.card = min (2 * (t - 1)) d) :
    (insert d E).card = min (2 * t - 1) (d + 1) := by
  rw [Finset.card_insert_of_notMem (fun h => (Nat.lt_irrefl d) (Finset.mem_range.mp (hE h))),
    hcard]
  omega

private theorem zmodTwo_nonzero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

theorem determinesExactDegree_zmodTwo_iff_fixed (x : ι → ZMod 2) (d t : ℕ) :
    DeterminesExactDegree x d t ↔ DeterminesFixedLeading x d t 1 := by
  constructor
  · intro h f g hf hg hfc hgc _ _ hs
    exact h f g hf hg hfc hgc (Set.mem_univ _) (Set.mem_univ _) hs
  · intro h f g hf hg hfc hgc _ _ hs
    exact h f g hf hg hfc hgc
      (Set.mem_singleton_iff.mpr (zmodTwo_nonzero_eq_one _ (degree_data hf).2))
      (Set.mem_singleton_iff.mpr (zmodTwo_nonzero_eq_one _ (degree_data hg).2)) hs

theorem determinesExactDegree_zmodTwo_iff_determinesLower (x : ι → ZMod 2) (d t : ℕ)
    (ht : 1 ≤ t) : DeterminesExactDegree x d t ↔ DeterminesLower x d (t - 1) :=
  (determinesExactDegree_zmodTwo_iff_fixed x d t).trans
    (determinesFixedLeading_iff_determinesLower x d t 1 ht one_ne_zero)

theorem determinesExactDegree_zmodTwo_iff_determinantal_annihilator (x : ι → ZMod 2) (d t : ℕ)
    (ht : 1 ≤ t) :
    DeterminesExactDegree x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d → E.card = min (2 * (t - 1)) d →
        (fullMinorIdeal (evaluationMatrix x E)).annihilator = ⊥ :=
  (determinesExactDegree_zmodTwo_iff_fixed x d t).trans
    (determinesFixedLeading_iff_determinantal_annihilator x d t 1 ht one_ne_zero)

/-- Every designated term survives when all assigned coefficients are nonzero. -/
private theorem support_polynomialOn_eq (E : Finset ℕ) (c : E → R) (hc : ∀ j, c j ≠ 0) :
    (polynomialOn E c).support = E := by
  apply Finset.Subset.antisymm (polynomialOn_support E c)
  intro j hj
  exact mem_support_iff.mpr (by rw [coeff_polynomialOn, dif_pos hj]; exact hc ⟨j, hj⟩)

/-- In a ring with a third element, exactly s terms on each side can
realize every difference with at most 2s terms in a universe of size ≥ s. -/
theorem exact_support_difference_of_third (D : Finset ℕ) (s : ℕ)
    (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) (hfit : s ≤ D.card)
    (p : R[X]) (hp : p.support ⊆ D) (hps : p.support.card ≤ 2 * s) :
    ∃ f g : R[X], f.support ⊆ D ∧ g.support ⊆ D ∧
      f.support.card = s ∧ g.support.card = s ∧ p = f - g := by
  classical
  let S := p.support
  let r := S.card - s
  let k := s - (S.card - r)
  have hps' : S.card ≤ 2 * s := hps
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq (s := S) (n := r) (Nat.sub_le _ _)
  have hble : r ≤ (S \ A).card := by
    rw [Finset.card_sdiff_of_subset hA, hAc]
    dsimp [r]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq hble
  have hBS : B ⊆ S := hB.trans Finset.sdiff_subset
  have hple : k ≤ (D \ S).card := by
    rw [Finset.card_sdiff_of_subset (show S ⊆ D from hp)]
    dsimp [k, r]
    omega
  obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hple
  let F := (S \ B) ∪ P
  let G := (S \ A) ∪ P
  have hdisj (T : Finset ℕ) (hT : T ⊆ S) : Disjoint T P :=
    Finset.disjoint_left.mpr fun _ hj hk => (Finset.mem_sdiff.mp (hP hk)).2 (hT hj)
  have hcounts (U : Finset ℕ) (hU : U ⊆ S) (hc : U.card = r) :
      ((S \ U) ∪ P).card = s := by
    rw [Finset.card_union_of_disjoint (hdisj _ Finset.sdiff_subset),
      Finset.card_sdiff_of_subset hU, hc, hPc]
    dsimp [k, r]
    omega
  have hPF : P ⊆ D := hP.trans Finset.sdiff_subset
  have hFD : F ⊆ D := Finset.union_subset (Finset.sdiff_subset.trans hp) hPF
  have hGD : G ⊆ D := Finset.union_subset (Finset.sdiff_subset.trans hp) hPF
  choose a b ha hb hab using fun j => exists_nonzero_sub_eq third (p.coeff j)
  haveI : Nontrivial R := nontrivial_of_ne (a 0) 0 (ha 0)
  let fc (j : F) := if j.val ∈ A then p.coeff j.val else if j.val ∈ S then a j.val else 1
  let gc (j : G) := if j.val ∈ B then -p.coeff j.val else if j.val ∈ S then b j.val else 1
  let f := polynomialOn F fc
  let g := polynomialOn G gc
  have hf : f.support = F := by
    apply support_polynomialOn_eq
    intro j
    unfold fc
    split_ifs with hj
    · exact mem_support_iff.mp (hA hj)
    · exact ha _
    · exact one_ne_zero
  have hg : g.support = G := by
    apply support_polynomialOn_eq
    intro j
    unfold gc
    split_ifs with hj
    · exact neg_ne_zero.mpr (mem_support_iff.mp (hBS hj))
    · exact hb _
    · exact one_ne_zero
  refine ⟨f, g, hf ▸ hFD, hg ▸ hGD, hf ▸ hcounts B hBS hBc, hg ▸ hcounts A hA hAc, ?_⟩
  ext j
  change p.coeff j = (polynomialOn F fc - polynomialOn G gc).coeff j
  rw [coeff_sub, coeff_polynomialOn, coeff_polynomialOn]
  by_cases hs : j ∈ S
  · have hnp : j ∉ P := fun h => (Finset.mem_sdiff.mp (hP h)).2 hs
    by_cases hjA : j ∈ A
    · have hjB : j ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 hjA
      simp [fc, F, G, hs, hnp, hjA, hjB]
    · by_cases hjB : j ∈ B
      · simp [gc, F, G, hs, hnp, hjA, hjB]
      · simpa [fc, gc, F, G, hs, hnp, hjA, hjB] using (hab j).symm
  · have hjA : j ∉ A := fun h => hs (hA h)
    have hjB : j ∉ B := fun h => hs (hBS h)
    have hz : p.coeff j = 0 := notMem_support_iff.mp hs
    by_cases hjP : j ∈ P <;> simp [fc, gc, F, G, hs, hjA, hjB, hjP, hz]

/-- Exact t terms, together with an exact degree and permitted leading set. -/
def DeterminesExactDegreeExactTermsWith (x : ι → R) (d t : ℕ) (A : Set R) : Prop :=
  ∀ f g : R[X], f.degree = d → g.degree = d →
    f.support.card = t → g.support.card = t →
    f.coeff d ∈ A → g.coeff d ∈ A →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

/-- Over rings with a third element, exact sparsity has the same collision
obstruction as at-most sparsity whenever t ≤ d+1. -/
theorem determinesExactDegreeExactTermsWith_iff (x : ι → R) (d t : ℕ) (A : Set R)
    (ht : 1 ≤ t) (hfit : t ≤ d + 1) (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) :
    DeterminesExactDegreeExactTermsWith x d t A ↔ DeterminesExactDegreeWith x d t A := by
  constructor
  · intro h
    apply (determinesExactDegreeWith_iff_difference_kernel x d t A ht).mpr
    intro a ham b hbm ha hb p hp hz
    have hfit' : t - 1 ≤ (Finset.range d).card := by simp; omega
    obtain ⟨f, g, hf, hg, hfc, hgc, he⟩ :=
      exact_support_difference_of_third (Finset.range d) (t - 1) third hfit' p hp.1 hp.2
    have hnF : (monomial d a + f).support.card = t := by rw [card_top_add hf ha, hfc]; omega
    have hnG : (monomial d b + g).support.card = t := by rw [card_top_add hg hb, hgc]; omega
    have hd : (monomial d a + f) - (monomial d b + g) = monomial d (a - b) + p := by
      rw [top_sub, ← he]
    have hobs : ∀ i, (monomial d a + f).eval (x i) = (monomial d b + g).eval (x i) :=
      fun i => sub_eq_zero.mp (by rw [← eval_sub, hd]; exact hz i)
    have heq := h _ _ (exact_degree_top_add hf ha) (exact_degree_top_add hg hb) hnF hnG
      (by simpa [coeff_top_add hf] using ham) (by simpa [coeff_top_add hg] using hbm) hobs
    rw [← hd, heq, sub_self]
  · intro h f g hf hg hfc hgc ha hb hs
    exact h f g hf hg hfc.le hgc.le ha hb hs

private theorem binary_support_sub (f g : (ZMod 2)[X]) :
    (f - g).support = (f.support \ g.support) ∪ (g.support \ f.support) := by
  ext j
  rw [mem_support_iff, coeff_sub, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
  by_cases hf : j ∈ f.support <;> by_cases hg : j ∈ g.support
  · simp [hf, hg, zmodTwo_nonzero_eq_one _ (mem_support_iff.mp hf),
      zmodTwo_nonzero_eq_one _ (mem_support_iff.mp hg)]
  · simp [hf, hg, zmodTwo_nonzero_eq_one _ (mem_support_iff.mp hf),
      notMem_support_iff.mp hg]
  · simp [hf, hg, notMem_support_iff.mp hf, zmodTwo_nonzero_eq_one _ (mem_support_iff.mp hg)]
  · simp [hf, hg, notMem_support_iff.mp hf, notMem_support_iff.mp hg]

private theorem binary_eq_of_support_eq (p q : (ZMod 2)[X]) (he : p.support = q.support) :
    p = q := by
  ext j
  by_cases h : j ∈ p.support
  · rw [zmodTwo_nonzero_eq_one _ (mem_support_iff.mp h),
      zmodTwo_nonzero_eq_one _ (mem_support_iff.mp (he ▸ h))]
  · rw [notMem_support_iff.mp h, notMem_support_iff.mp (he ▸ h)]

/-- Binary differences of two exact s-term polynomials are precisely the
even supports of size at most 2 min(s, |D|-s) in the allowed universe. -/
theorem zmodTwo_exact_support_difference_iff (D : Finset ℕ) (s : ℕ)
    (hfit : s ≤ D.card) (p : (ZMod 2)[X]) :
    (p.support ⊆ D ∧ Even p.support.card ∧ p.support.card ≤ 2 * min s (D.card - s)) ↔
      ∃ f g : (ZMod 2)[X], f.support ⊆ D ∧ g.support ⊆ D ∧
        f.support.card = s ∧ g.support.card = s ∧ p = f - g := by
  constructor
  · rintro ⟨hp, ⟨r, hr⟩, hcap⟩
    let S := p.support
    have hr' : S.card = r + r := hr
    have hrle : r ≤ min s (D.card - s) := by omega
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq (s := S) (n := r) (by omega)
    let B := S \ A
    have hBc : B.card = r := by rw [Finset.card_sdiff_of_subset hA, hAc]; omega
    have hPfit : s - r ≤ (D \ S).card := by
      rw [Finset.card_sdiff_of_subset (show S ⊆ D from hp)]
      omega
    obtain ⟨P, hP, hPc⟩ := Finset.exists_subset_card_eq hPfit
    let f := polynomialOn (A ∪ P) (fun _ => (1 : ZMod 2))
    let g := polynomialOn (B ∪ P) (fun _ => (1 : ZMod 2))
    have hf : f.support = A ∪ P := support_polynomialOn_eq _ _ (fun _ => one_ne_zero)
    have hg : g.support = B ∪ P := support_polynomialOn_eq _ _ (fun _ => one_ne_zero)
    have hcounts (T : Finset ℕ) (hT : T ⊆ S) (hc : T.card = r) :
        (T ∪ P).card = s := by
      have hdisj : Disjoint T P :=
        Finset.disjoint_left.mpr fun _ h₁ h₂ => (Finset.mem_sdiff.mp (hP h₂)).2 (hT h₁)
      rw [Finset.card_union_of_disjoint hdisj, hc, hPc]
      omega
    have hPD : P ⊆ D := hP.trans Finset.sdiff_subset
    refine ⟨f, g, hf ▸ Finset.union_subset (hA.trans hp) hPD,
      hg ▸ Finset.union_subset (Finset.sdiff_subset.trans hp) hPD,
      hf ▸ hcounts A hA hAc, hg ▸ hcounts B Finset.sdiff_subset hBc, ?_⟩
    apply binary_eq_of_support_eq
    rw [binary_support_sub, hf, hg]
    change S = _
    ext j
    have hAS : j ∈ A → j ∈ S := fun h => hA h
    have hPS : j ∈ P → j ∉ S := fun h => (Finset.mem_sdiff.mp (hP h)).2
    by_cases hjS : j ∈ S <;> by_cases hjA : j ∈ A <;> by_cases hjP : j ∈ P <;>
      simp_all [B, Finset.mem_sdiff, Finset.mem_union]
  · rintro ⟨f, g, hf, hg, hfc, hgc, rfl⟩
    let L := f.support \ g.support
    let M := g.support \ f.support
    have hdisj : Disjoint L M := Finset.disjoint_left.mpr fun _ h₁ h₂ =>
      (Finset.mem_sdiff.mp h₁).2 (Finset.mem_sdiff.mp h₂).1
    have hL := Finset.card_sdiff_add_card_inter f.support g.support
    have hM := Finset.card_sdiff_add_card_inter g.support f.support
    rw [Finset.inter_comm g.support f.support] at hM
    change L.card + (f.support ∩ g.support).card = f.support.card at hL
    change M.card + (f.support ∩ g.support).card = g.support.card at hM
    have hueq : M.card = L.card := by omega
    have hU := Finset.card_sdiff_add_card f.support g.support
    change L.card + g.support.card = (f.support ∪ g.support).card at hU
    have hUle := Finset.card_le_card (Finset.union_subset hf hg)
    rw [binary_support_sub]
    change L ∪ M ⊆ D ∧ Even ((L ∪ M).card) ∧ (L ∪ M).card ≤ _
    refine ⟨Finset.union_subset (Finset.sdiff_subset.trans hf) (Finset.sdiff_subset.trans hg), ?_, ?_⟩
    · exact ⟨L.card, by rw [Finset.card_union_of_disjoint hdisj, hueq]⟩
    · rw [Finset.card_union_of_disjoint hdisj, hueq]
      omega

private theorem zmodTwo_top_sub_eq_erases {d : ℕ} {f g : (ZMod 2)[X]}
    (hf : f.degree = d) (hg : g.degree = d) :
    f - g = f.erase d - g.erase d := by
  calc
    _ = (monomial d (f.coeff d) + f.erase d) - (monomial d (g.coeff d) + g.erase d) :=
      congrArg₂ (· - ·) (monomial_add_erase f d).symm (monomial_add_erase g d).symm
    _ = _ := by
      rw [top_sub, zmodTwo_nonzero_eq_one _ (degree_data hf).2,
        zmodTwo_nonzero_eq_one _ (degree_data hg).2, sub_self, monomial_zero_right, zero_add]

private theorem card_erase_top_exact {d t : ℕ} {p : R[X]} (hd : p.degree = d)
    (hc : p.support.card = t) : (p.erase d).support.card = t - 1 := by
  have h := Finset.card_erase_add_one (mem_support_iff.mpr (degree_data hd).2)
  rw [support_erase]
  omega

theorem determinesExactDegreeExactTerms_zmodTwo_iff_even_kernel (x : ι → ZMod 2) (d t : ℕ)
    (ht : 1 ≤ t) (hfit : t ≤ d + 1) :
    DeterminesExactDegreeExactTermsWith x d t Set.univ ↔
      ∀ p : (ZMod 2)[X], p.support ⊆ Finset.range d → Even p.support.card →
        p.support.card ≤ 2 * min (t - 1) (d - (t - 1)) → Vanishes x p → p = 0 := by
  have hfit' : t - 1 ≤ (Finset.range d).card := by rw [Finset.card_range]; omega
  constructor
  · intro h p hp hEven hcap hz
    obtain ⟨f, g, hf, hg, hfc, hgc, hdiff⟩ :=
      (zmodTwo_exact_support_difference_iff (Finset.range d) (t - 1) hfit' p).mp
        ⟨hp, hEven, by simpa using hcap⟩
    have ha : (1 : ZMod 2) ≠ 0 := one_ne_zero
    have hfc' : (monomial d 1 + f).support.card = t := by rw [card_top_add hf ha, hfc]; omega
    have hgc' : (monomial d 1 + g).support.card = t := by rw [card_top_add hg ha, hgc]; omega
    have he : (monomial d 1 + f) - (monomial d 1 + g) = p := by
      rw [top_sub, sub_self, monomial_zero_right, zero_add, ← hdiff]
    have hobs : ∀ i, (monomial d 1 + f).eval (x i) = (monomial d 1 + g).eval (x i) :=
      fun i => sub_eq_zero.mp (by rw [← eval_sub, he]; exact hz i)
    have hsame := h _ _ (exact_degree_top_add hf ha) (exact_degree_top_add hg ha)
      hfc' hgc' (Set.mem_univ _) (Set.mem_univ _) hobs
    rw [← he, hsame, sub_self]
  · intro h f g hf hg hfc hgc _ _ hobs
    have he := zmodTwo_top_sub_eq_erases hf hg
    obtain ⟨hs, hEven, hcap⟩ :=
      (zmodTwo_exact_support_difference_iff (Finset.range d) (t - 1) hfit' (f - g)).mpr
        ⟨f.erase d, g.erase d, (erase_top_lower hf hfc.le).1, (erase_top_lower hg hgc.le).1,
          card_erase_top_exact hf hfc, card_erase_top_exact hg hgc, he⟩
    exact sub_eq_zero.mp (h _ hs hEven (by simpa using hcap) fun i => by rw [eval_sub, hobs, sub_self])

/-- An extra sample at 1 checks the parity of support size over F₂. -/
def withOneSample (x : ι → ZMod 2) : Option ι → ZMod 2 :=
  Option.elim' 1 x

@[simp] theorem evaluationMatrix_withOneSample_none (x : ι → ZMod 2) (E : Finset ℕ) (e : E) :
    evaluationMatrix (withOneSample x) E none e = 1 := by
  simp [evaluationMatrix, withOneSample]

private theorem binary_eval_one (p : (ZMod 2)[X]) :
    p.eval 1 = (p.support.card : ZMod 2) := by
  rw [eval_eq_sum, sum_def]
  calc
    _ = ∑ j ∈ p.support, (1 : ZMod 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp [zmodTwo_nonzero_eq_one _ (mem_support_iff.mp hj)]
    _ = _ := by simp

private theorem vanishes_withOneSample (x : ι → ZMod 2) (p : (ZMod 2)[X]) :
    Vanishes (withOneSample x) p ↔ Even p.support.card ∧ Vanishes x p := by
  constructor
  · intro h
    have h1 : p.eval 1 = 0 := h none
    exact ⟨ZMod.natCast_eq_zero_iff_even.mp (binary_eval_one p ▸ h1), fun i => h (some i)⟩
  · rintro ⟨hEven, hz⟩ (none | i)
    · change p.eval 1 = 0
      exact (binary_eval_one p).trans (ZMod.natCast_eq_zero_iff_even.mpr hEven)
    · exact hz i

/-- Exact-degree, exact-term-count binary criterion. Appending x=1 is
the all-ones row, and every tested exponent is strictly below d. -/
theorem determinesExactDegreeExactTerms_zmodTwo_iff_determinantal_annihilator
    (x : ι → ZMod 2) (d t : ℕ) (ht : 1 ≤ t) (hfit : t ≤ d + 1) :
    DeterminesExactDegreeExactTermsWith x d t Set.univ ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range d →
        E.card = 2 * min (t - 1) (d - (t - 1)) →
        (fullMinorIdeal (evaluationMatrix (withOneSample x) E)).annihilator = ⊥ := by
  let k := 2 * min (t - 1) (d - (t - 1))
  have hkd : k ≤ d := by dsimp [k]; omega
  have hrew :
      (∀ p : (ZMod 2)[X], p.support ⊆ Finset.range d → Even p.support.card →
        p.support.card ≤ k → Vanishes x p → p = 0) ↔
      (∀ p : (ZMod 2)[X], LowerSparse d k p → Vanishes (withOneSample x) p → p = 0) := by
    simp only [vanishes_withOneSample]
    exact ⟨fun h p hp hz => h p hp.1 hz.1 hp.2 hz.2,
      fun h p hsub hev hcard hz => h p ⟨hsub, hcard⟩ ⟨hev, hz⟩⟩
  rw [determinesExactDegreeExactTerms_zmodTwo_iff_even_kernel x d t ht hfit, hrew,
    lower_kernel_iff_support_tests]
  simpa only [min_eq_left hkd] using support_tests_iff_max_ideals (withOneSample x) d k id monotone_id

/-- At-most degree, exact support count. -/
def DeterminesBoundedDegreeExactTerms (x : ι → R) (d t : ℕ) : Prop :=
  ∀ f g : R[X], f.natDegree ≤ d → g.natDegree ≤ d →
    f.support.card = t → g.support.card = t →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

private theorem boundedExactTerms_iff_lift_fixed (x : ι → R) (d t : ℕ) (a : R)
    (ha : a ≠ 0) :
    DeterminesBoundedDegreeExactTerms x d t ↔
      DeterminesExactDegreeExactTermsWith x (d + 1) (t + 1) {a} := by
  constructor
  · intro h f g hf hg hfc hgc hfa hga hs
    have hF : monomial (d + 1) a + f.erase (d + 1) = f := by
      rw [← Set.mem_singleton_iff.mp hfa, monomial_add_erase]
    have hG : monomial (d + 1) a + g.erase (d + 1) = g := by
      rw [← Set.mem_singleton_iff.mp hga, monomial_add_erase]
    have hfd := (lowerSparse_succ_iff d t _).mp (by simpa using erase_top_lower hf hfc.le)
    have hgd := (lowerSparse_succ_iff d t _).mp (by simpa using erase_top_lower hg hgc.le)
    have hErase := h _ _ hfd.1 hgd.1 (by simpa using card_erase_top_exact hf hfc)
      (by simpa using card_erase_top_exact hg hgc) (fun i => by
        have he := hs i
        rw [← hF, ← hG, eval_add, eval_add] at he
        exact add_left_cancel he)
    rw [← hF, ← hG, hErase]
  · intro h f g hf hg hfc hgc hs
    have hF := supp_subset_range (Nat.lt_succ_of_le hf)
    have hG := supp_subset_range (Nat.lt_succ_of_le hg)
    apply add_left_cancel (a := monomial (d + 1) a)
    exact h _ _ (exact_degree_top_add hF ha) (exact_degree_top_add hG ha)
      (by rw [card_top_add hF ha, hfc]) (by rw [card_top_add hG ha, hgc])
      (by rw [Set.mem_singleton_iff, coeff_top_add hF])
      (by rw [Set.mem_singleton_iff, coeff_top_add hG]) (fun i => by rw [eval_add, eval_add, hs])

theorem determinesBoundedDegreeExactTerms_iff_determinesSparse (x : ι → R) (d t : ℕ)
    (hfit : t ≤ d + 1) (third : ∃ u : R, u ≠ 0 ∧ u ≠ 1) :
    DeterminesBoundedDegreeExactTerms x d t ↔ DeterminesSparse x d t := by
  haveI : Nontrivial R := by obtain ⟨u, hu, _⟩ := third; exact nontrivial_of_ne u 0 hu
  rw [boundedExactTerms_iff_lift_fixed x d t 1 one_ne_zero,
    determinesExactDegreeExactTermsWith_iff x (d + 1) (t + 1) {1} (by omega) (by omega) third]
  simpa [DeterminesLower, DeterminesSparse, lowerSparse_succ_iff] using
    determinesFixedLeading_iff_determinesLower x (d + 1) (t + 1) 1 (by omega) one_ne_zero

theorem determinesBoundedDegreeExactTerms_zmodTwo_iff_determinantal_annihilator
    (x : ι → ZMod 2) (d t : ℕ) (hfit : t ≤ d + 1) :
    DeterminesBoundedDegreeExactTerms x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range (d + 1) →
        E.card = 2 * min t (d + 1 - t) →
        (fullMinorIdeal (evaluationMatrix (withOneSample x) E)).annihilator = ⊥ := by
  have hsame :
      DeterminesExactDegreeExactTermsWith x (d + 1) (t + 1) {1} ↔
        DeterminesExactDegreeExactTermsWith x (d + 1) (t + 1) Set.univ := by
    constructor
    · intro h f g hf hg hfc hgc _ _ hs
      exact h f g hf hg hfc hgc
        (Set.mem_singleton_iff.mpr (zmodTwo_nonzero_eq_one _ (degree_data hf).2))
        (Set.mem_singleton_iff.mpr (zmodTwo_nonzero_eq_one _ (degree_data hg).2)) hs
    · intro h f g hf hg hfc hgc _ _ hs
      exact h f g hf hg hfc hgc (Set.mem_univ _) (Set.mem_univ _) hs
  rw [boundedExactTerms_iff_lift_fixed x d t 1 one_ne_zero, hsame,
    determinesExactDegreeExactTerms_zmodTwo_iff_determinantal_annihilator x (d + 1) (t + 1)
      (by omega) (by omega)]
  simp

end GrenetMcCoy
