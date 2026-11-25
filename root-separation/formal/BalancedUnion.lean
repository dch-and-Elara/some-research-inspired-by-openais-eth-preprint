import SourceDensity

/-! A coordinate cut balances the vertices carrying the pin signs. The number
of symbols assigned to a side can be arbitrary. -/

namespace BalancedUnion

open scoped BigOperators

variable {A V : Type*}

private theorem take_small (w : A → ℚ) (q : ℚ) (hq : 0 < q) (hsmall : ∀ a, w a < q)
    (t : Finset A) (ht : q ≤ ∑ a ∈ t, w a) :
    ∃ s ⊆ t, q ≤ ∑ a ∈ s, w a ∧ (∑ a ∈ s, w a) < 2 * q := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty] at ht
    exact False.elim (not_lt_of_ge ht hq)
  | @insert a t ha ih =>
    by_cases h : q ≤ ∑ b ∈ t, w b
    · obtain ⟨s, hs, hlo, hhi⟩ := ih h
      exact ⟨s, hs.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert a t, Finset.Subset.rfl, ht, ?_⟩
      rw [Finset.sum_insert ha]
      linarith only [lt_of_not_ge h, hsmall a]

/-- A probability distribution whose atoms have mass at most 3/4 has a set
whose mass is between 1/4 and 3/4. The proof only uses the total and atom cap. -/
theorem exists_quarter_union [Fintype A] (w : A → ℚ) (hmass : ∑ a, w a = 1)
    (hcap : ∀ a, w a ≤ 3 / 4) :
    ∃ s : Finset A, 1 / 4 ≤ ∑ a ∈ s, w a ∧ (∑ a ∈ s, w a) ≤ 3 / 4 := by
  classical
  by_cases h : ∃ a, 1 / 4 ≤ w a
  · obtain ⟨a, ha⟩ := h
    exact ⟨{a}, by simpa using ha, by simpa using hcap a⟩
  · have hsmall (a : A) : w a < 1 / 4 := lt_of_not_ge fun ha => h ⟨a,ha⟩
    obtain ⟨s, _, hlo, hhi⟩ := take_small w (1 / 4) (by norm_num) hsmall Finset.univ
      (by rw [hmass]; norm_num)
    exact ⟨s, hlo, by linarith only [hhi]⟩

variable [Fintype V] [Fintype A] [DecidableEq A]

def vertexUnion (L : V → A) (s : Finset A) : Finset V :=
  Finset.univ.filter fun v => L v ∈ s

omit [Fintype A] in
theorem union_mass (L : V → A) (s : Finset A) :
    (∑ a ∈ s, EmpiricalCutMoments.empiricalLaw L a) =
      ((vertexUnion L s).card : ℚ) / Fintype.card V := by
  have hc : (∑ a ∈ s, SourceDensity.fiberCount L a) = (vertexUnion L s).card :=
    Finset.sum_card_fiberwise_eq_card_filter Finset.univ s L
  calc
    _ = (∑ a ∈ s, (SourceDensity.fiberCount L a : ℚ)) / (Fintype.card V : ℚ) := by
      simp only [EmpiricalCutMoments.empiricalLaw, SourceDensity.fiberCount, div_eq_mul_inv,
        Finset.sum_mul]
    _ = _ := by rw [← Nat.cast_sum, hc]

theorem exists_balanced_vertex_union_of_law [Nonempty V] (L : V → A)
    (hcap : ∀ a, EmpiricalCutMoments.empiricalLaw L a ≤ 3 / 4) :
    ∃ s : Finset A, (1 / 4 : ℚ) * Fintype.card V ≤
      (min (vertexUnion L s).card (Fintype.card V - (vertexUnion L s).card) : ℕ) := by
  obtain ⟨s, hlo, hhi⟩ := exists_quarter_union _ (EmpiricalCutMoments.sum_empiricalLaw L) hcap
  rw [union_mass] at hlo hhi
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hlow := (le_div_iff₀ hV).1 hlo
  have hhigh := (div_le_iff₀ hV).1 hhi
  have hle := Finset.card_le_univ (vertexUnion L s)
  refine ⟨s, ?_⟩
  rw [Nat.cast_min, Nat.cast_sub hle]
  exact le_min hlow (by linarith only [hhigh])

theorem exists_balanced_vertex_union [Nonempty V] (L : V → A)
    (hcap : ∀ a, (SourceDensity.fiberCount L a : ℚ) ≤ (3 / 4 : ℚ) * Fintype.card V) :
    ∃ s : Finset A, (1 / 4 : ℚ) * Fintype.card V ≤
      (min (vertexUnion L s).card (Fintype.card V - (vertexUnion L s).card) : ℕ) := by
  apply exists_balanced_vertex_union_of_law
  intro a
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := V))).2
  exact hcap a

section Source

variable {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]

theorem single_coordinate_fiber (i : I) (a : A) :
    SourceDensity.fiberCount (fun c : (I → A) × (I → A) => c.1 i) a =
      (Fintype.card A) ^ (Fintype.card I - 1) * (Fintype.card A) ^ Fintype.card I := by
  classical
  have he : SourceDensity.fiberCount (fun c : (I → A) × (I → A) => c.1 i) a =
      SourceDensity.fiberCount (SourceDensity.firstCoordinates ({i} : Finset I)) (fun _ => a) := by
    apply congrArg Finset.card
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
    constructor
    · intro hi j
      change c.1 j.1 = a
      rw [Finset.mem_singleton.mp j.2]
      exact hi
    · intro h
      exact h ⟨i, Finset.mem_singleton_self i⟩
  rw [he, SourceDensity.ordered_cell_projection_regular, Finset.card_singleton]

/-- With at least 27 symbols, the source's 20-times-uniform bound supplies an
actual quarter-balanced union at each coordinate, counted in pin vertices. -/
theorem source_balanced_unions [Nonempty V] [DecidableEq V]
    (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate cell Δ) (hports : Fintype.card P = 10 * Fintype.card V)
    (hA : 27 ≤ Fintype.card A) :
    ∃ symbols : I → Finset A, ∀ i, (1 / 4 : ℚ) * Fintype.card V ≤
      (min (EmpiricalCutMoments.labelCut (fun v => (cell (pin v)).1) id symbols i).card
        (Fintype.card V - (EmpiricalCutMoments.labelCut (fun v => (cell (pin v)).1) id symbols i).card) : ℕ) := by
  classical
  have hc : 20 * ProductVariance.uniformWeight A ≤ 3 / 4 := by
    have ha : (27 : ℚ) ≤ Fintype.card A := by exact_mod_cast hA
    have hp : (0 : ℚ) < Fintype.card A := by linarith only [ha]
    rw [ProductVariance.uniformWeight, ← div_eq_mul_inv, div_le_iff₀ hp]
    linarith only [ha]
  have hsingle (i : I) (a : A) :
      EmpiricalCutMoments.empiricalLaw (fun v => (cell (pin v)).1 i) a ≤ 3 / 4 := by
    exact (SourceDensity.pin_marginal_twenty pin cell Δ cert (fun c => c.1 i) _
      (single_coordinate_fiber i) hports a).trans hc
  choose symbols hs using fun i => exists_balanced_vertex_union_of_law _ (hsingle i)
  exact ⟨symbols, hs⟩

end Source

section GroupProduct

variable {R : Type*} [CommMonoid R] (L : V → A)

/-- One side's product takes only variables whose symbol lies on that side. -/
def localProduct (g : ∀ a, ({v // L v = a} → Bool) → R) (s : Finset A)
    (x : {v // L v ∈ s} → Bool) : R :=
  ∏ a : s, g a.1 (fun v => x ⟨v.1, (v.2.symm ▸ a.2)⟩)

omit [Fintype V] in
theorem group_product_separates (g : ∀ a, ({v // L v = a} → Bool) → R) (s : Finset A)
    (x : V → Bool) :
    (∏ a, g a (fun v => x v.1)) =
      localProduct L g s (fun v => x v.1) * localProduct L g sᶜ (fun v => x v.1) := by
  let f (a : A) := g a (fun v => x v.1)
  change (∏ a, f a) = (∏ a : s, f a.1) * ∏ a : (sᶜ : Finset A), f a.1
  rw [Finset.prod_coe_sort s f, Finset.prod_coe_sort sᶜ f]
  exact (Finset.prod_mul_prod_compl s f).symm

end GroupProduct

#print axioms exists_quarter_union
#print axioms union_mass
#print axioms exists_balanced_vertex_union_of_law
#print axioms exists_balanced_vertex_union
#print axioms single_coordinate_fiber
#print axioms source_balanced_unions
#print axioms group_product_separates

end BalancedUnion
