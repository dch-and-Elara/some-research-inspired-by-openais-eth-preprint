import J7SourceLabels
import J7SourceConditioning
import GuardExpectation

/-!
# J7 source assembly

Combine the physical shared-block incidence bound, the exactly local
conditional expectation formula, and finite positive-mass conditioning.
All laws below may be nonuniform and have zero-mass alternatives.
-/

open scoped BigOperators Classical

namespace J7SourceAssembly

noncomputable section

set_option maxHeartbeats 1500000

local instance (priority := 100000) {X : Type*} : DecidableEq X :=
  fun _ _ => Classical.propDecidable _

open J7SourceLabels J7SourceConditioning

section LegalConditioning

variable {Ω : Type*} [Fintype Ω]

/-- A choice from the support of a rational law attains or improves its
mean. Picking an arbitrary minimum over zero-mass outcomes is not needed. -/
theorem exists_positive_le_mean (μ f : Ω → ℚ) (nonneg : ∀ x, 0 ≤ μ x)
    (norm : ∑ x, μ x = 1) :
    ∃ x, 0 < μ x ∧ f x ≤ expect μ f := by
  by_contra bad
  have hgt (x : Ω) (hx : 0 < μ x) : expect μ f < f x :=
    lt_of_not_ge fun hh => bad ⟨x, hx, hh⟩
  have present : ∃ x, 0 < μ x := by
    by_contra hz
    have h0 (x : Ω) : μ x = 0 :=
      le_antisymm (le_of_not_gt fun hx => hz ⟨x,hx⟩) (nonneg x)
    simp [h0] at norm
  let g := fun x => μ x * (f x - expect μ f)
  have hg (x : Ω) : 0 ≤ g x := by
    by_cases hx : μ x = 0
    · simp [g, hx]
    · exact mul_nonneg (nonneg x) (sub_nonneg.mpr (hgt x (lt_of_le_of_ne (nonneg x) (Ne.symm hx))).le)
  obtain ⟨x, hx⟩ := present
  have strict : 0 < ∑ z, g z :=
    Finset.sum_pos' (fun z _ => hg z)
      ⟨x, Finset.mem_univ x, mul_pos hx (sub_pos.mpr (hgt x hx))⟩
  have hsum : (∑ z, g z) = 0 := by
    unfold g
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, norm, one_mul]
    exact sub_self _
  rw [hsum] at strict
  exact (lt_irrefl 0) strict

variable {B T : Type*} [Fintype B] [Fintype T]

/-- Each conditional-expectation step has a supported choice. In
particular, the forced nonzero pin offset is retained. -/
theorem exists_legal_fix (w : B → T → ℚ) (h0 : ∀ b x, 0 ≤ w b x)
    (h1 : ∀ b, ∑ x, w b x = 1) (f : (B → T) → ℚ) (b : B) :
    ∃ x, 0 < w b x ∧
      GuardExpectation.average (GuardExpectation.fixAt w b x) f ≤ GuardExpectation.average w f := by
  obtain ⟨x, hx, hv⟩ := exists_positive_le_mean (w b)
    (fun x => GuardExpectation.average (GuardExpectation.fixAt w b x) f) (h0 b) (h1 b)
  refine ⟨x,hx,?_⟩
  rw [GuardExpectation.split_average_fixAt w f b]
  exact hv

theorem exists_legal_fixOn (reference : B → T) (s : Finset B) (w : B → T → ℚ)
    (h0 : ∀ b x, 0 ≤ w b x) (h1 : ∀ b, ∑ x, w b x = 1)
    (f : (B → T) → ℚ) :
    ∃ a, (∀ e ∈ s, 0 < w e (a e)) ∧
      GuardExpectation.average (GuardExpectation.fixOn w s a) f ≤ GuardExpectation.average w f := by
  induction s using Finset.induction_on generalizing w with
  | empty =>
    refine ⟨reference, by simp, ?_⟩
    have heq : GuardExpectation.fixOn w ∅ reference = w := by
      funext b x
      simp [GuardExpectation.fixOn]
    rw [heq]
  | insert b s hb ih =>
    obtain ⟨x, hx, hav⟩ := exists_legal_fix w h0 h1 f b
    obtain ⟨a, ha, hav'⟩ :=
      ih (GuardExpectation.fixAt w b x) (GuardExpectation.fixAt_nonneg w h0 b x)
        (GuardExpectation.fixAt_normalized w h1 b x)
    rw [GuardExpectation.fixOn_insert w hb] at hav'
    refine ⟨Function.update a b x, ?_, hav'.trans hav⟩
    intro i hi
    by_cases h : i = b
    · subst i
      simpa using hx
    · have his := (Finset.mem_insert.mp hi).resolve_left h
      simpa only [GuardExpectation.fixAt, if_neg h, Function.update_of_ne h] using ha i his

/-- Legal final outcome obtained by the finite sequence of refinements. -/
theorem exists_legal_labeling_by_conditioning (reference : B → T) (w : B → T → ℚ)
    (h0 : ∀ b x, 0 ≤ w b x) (h1 : ∀ b, ∑ x, w b x = 1)
    (f : (B → T) → ℚ) :
    ∃ a, (∀ b, 0 < w b (a b)) ∧ f a ≤ GuardExpectation.average w f := by
  obtain ⟨a, ha, hav⟩ := exists_legal_fixOn reference Finset.univ w h0 h1 f
  rw [GuardExpectation.average_fixOn_univ] at hav
  exact ⟨a, fun b => ha b (Finset.mem_univ b), hav⟩

end LegalConditioning

section Physical

variable {A Pair Row Col W : Type*} [Fintype A] [AddCommGroup A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]

abbrev State (A Pair Row Col : Type*) := Block Pair Row Col → Draw A

def physicalLabel (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W)
    (z : State A Pair Row Col) : A × A := cell row col z e

def cellIndicator (row : W → Row) (col : W → OrdinaryColumn Pair Col) (e : Wire Pair W)
    (c : A × A) (z : State A Pair Row Col) : ℚ :=
  J7SourceConditioning.indicator (physicalLabel row col e z) c

omit [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] in
theorem indicator_depends (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (e : Wire Pair W) (c : A × A) :
    depends (fun b => b ∈ blockSupport row col e) (cellIndicator row col e c) := by
  intro z z' h
  unfold cellIndicator physicalLabel
  rw [cell_depends_on_support row col z z' e h]

omit [Fintype W] in
/-- Every collision score term can be evaluated under the current law
by enumerating only its at most four source blocks. This statement holds
for mixed free and fixed marginals. -/
theorem conditional_pair_at_most_four (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (w : Block Pair Row Col → Draw A → ℚ) (norm : ∀ b, ∑ x, w b x = 1)
    (reference : State A Pair Row Col) (e f : Wire Pair W) (c : A × A) :
    let s := blockSupport row col e ∪ blockSupport row col f
    s.card ≤ 4 ∧
      average w (fun z => cellIndicator row col e c z * cellIndicator row col f c z) =
        average (fun b : {b // b ∈ s} => w b)
          (fun t => cellIndicator row col e c (fill (fun b => b ∈ s) reference t) *
            cellIndicator row col f c (fill (fun b => b ∈ s) reference t)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · convert pair_support_at_most_four row col e f using 1
    congr 1
    exact Finset.ext fun b => by simp only [Finset.mem_union]
  have hlocal : depends (fun b => b ∈ blockSupport row col e ∪ blockSupport row col f)
      (fun z => cellIndicator row col e c z * cellIndicator row col f c z) := by
    intro z z' hz
    dsimp only
    rw [indicator_depends row col e c z z' (fun b hb => hz b (Finset.mem_union_left _ hb)),
      indicator_depends row col f c z z' (fun b hb => hz b (Finset.mem_union_right _ hb))]
  convert expectation_only_support w norm _ reference _ hlocal using 1
  congr 1
  exact Subsingleton.elim _ _

/-- Physical covariance bound, both on all wires and on the pin-only
sublist. The compact 16M bound is independent of the number of cells. -/
theorem physical_expected_bound (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (w : Block Pair Row Col → Draw A → ℚ) (h0 : ∀ b x, 0 ≤ w b x)
    (h1 : ∀ b, ∑ x, w b x = 1) (reference : State A Pair Row Col)
    (s : Finset (Wire Pair W)) :
    average w (varianceScore s (productWeight w) (physicalLabel row col)) ≤
      16 * (Fintype.card (Wire Pair W) : ℚ) := by
  have hnorm := productWeight_normalized w h1
  have hbase := expected_score_le_dependent (s := s) (weight := productWeight w)
    (label := physicalLabel row col) (dependentOn row col) (productWeight_nonneg w h0) hnorm
  have hind : ∀ e ∈ s, ∀ f ∈ s, f ∉ dependentOn row col e → ∀ c,
      expect (productWeight w) (fun z => cellIndicator row col e c z * cellIndicator row col f c z) =
        meanCell (productWeight w) (physicalLabel row col) e c *
          meanCell (productWeight w) (physicalLabel row col) f c := by
    intro e _ f _ hn c
    have hd : ∀ b, b ∈ blockSupport row col e → b ∈ blockSupport row col f → False :=
      fun b he hf => hn ((mem_dependentOn row col e f).2 ⟨b,he,hf⟩)
    simpa only [average, cellIndicator, meanCell] using
      expectation_disjoint_supports w h1 _ _ hd reference _
        _ (indicator_depends row col e c) (indicator_depends row col f c)
  have hfull : (∑ e : Wire Pair W, ((dependentOn row col e).card : ℚ)) ≤
      16 * (Fintype.card (Wire Pair W) : ℚ) := by
    have hnat : (∑ e : Wire Pair W, (dependentOn row col e).card) ≤ 16 * Fintype.card (Wire Pair W) := by
      refine ordered_dependent_pairs_le16 row col row_cap ?_ ?_
      · intro p
        convert clone_cap p using 1
        congr 1
        exact Finset.ext fun b => by simp only [Finset.mem_filter]
      · intro c
        convert col_cap c using 1
        congr 1
        exact Finset.ext fun b => by simp only [Finset.mem_filter]
    exact_mod_cast hnat
  exact (hbase hind).trans <|
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => Nat.cast_nonneg _)).trans hfull

/-- The two actual squared-load scores can be fixed together. Both
per-cell deviations are then bounded by the same finite budget, while
every selected block still lies in the support of its original law. -/
theorem select_physical_cells (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_cap : ∀ r, (Finset.univ.filter fun w : W => row w = r).card ≤ 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (w : Block Pair Row Col → Draw A → ℚ) (h0 : ∀ b x, 0 ≤ w b x)
    (h1 : ∀ b, ∑ x, w b x = 1) (reference : State A Pair Row Col)
    (pins : Finset (Wire Pair W)) :
    ∃ z : State A Pair Row Col,
      (∀ b, 0 < w b (z b)) ∧
      varianceScore Finset.univ (productWeight w) (physicalLabel row col) z +
        varianceScore pins (productWeight w) (physicalLabel row col) z ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) ∧
      ∀ c : A × A,
        (∑ e : Wire Pair W, centered (productWeight w) (physicalLabel row col) e c z)^2 ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) ∧
        (∑ e ∈ pins, centered (productWeight w) (physicalLabel row col) e c z)^2 ≤
          32 * (Fintype.card (Wire Pair W) : ℚ) := by
  let f := varianceScore Finset.univ (productWeight w) (physicalLabel row col)
  let g := varianceScore pins (productWeight w) (physicalLabel row col)
  obtain ⟨z,hz,hscore⟩ := exists_legal_labeling_by_conditioning reference w h0 h1 (fun z => f z + g z)
  have hf := physical_expected_bound row col row_cap clone_cap col_cap w h0 h1 reference Finset.univ
  have hg := physical_expected_bound row col row_cap clone_cap col_cap w h0 h1 reference pins
  rw [GuardExpectation.average_add] at hscore
  have hsum : f z + g z ≤ 32 * (Fintype.card (Wire Pair W) : ℚ) := by
    change f z + g z ≤ average w f + average w g at hscore
    change average w f ≤ _ at hf
    change average w g ≤ _ at hg
    linarith
  refine ⟨z,hz,hsum,?_⟩
  intro c
  have hfn : 0 ≤ f z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgn : 0 ≤ g z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcf : (∑ e : Wire Pair W, centered (productWeight w) (physicalLabel row col) e c z)^2 ≤ f z := by
    dsimp [f, varianceScore]
    exact Finset.single_le_sum (f := fun d : A × A =>
      (∑ e : Wire Pair W, centered (productWeight w) (physicalLabel row col) e d z)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  have hcg : (∑ e ∈ pins, centered (productWeight w) (physicalLabel row col) e c z)^2 ≤ g z := by
    dsimp [g, varianceScore]
    exact Finset.single_le_sum (f := fun d : A × A =>
      (∑ e ∈ pins, centered (productWeight w) (physicalLabel row col) e d z)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)
  exact ⟨hcf.trans (by linarith), hcg.trans (by linarith)⟩

end Physical

#print axioms exists_positive_le_mean
#print axioms exists_legal_fix
#print axioms exists_legal_labeling_by_conditioning
#print axioms conditional_pair_at_most_four
#print axioms physical_expected_bound
#print axioms select_physical_cells

end
end J7SourceAssembly
