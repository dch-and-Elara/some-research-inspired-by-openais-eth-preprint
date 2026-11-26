import GroupProducts
import LogarithmicBudget

/-! The main rational routine places an incidence in the ordered cell
(assignment-variable word, factor word). The second word owns its varying
literal coefficient. Start from the actual maximum-cell guarantee of the
source incidence-label lemma. The port/pin ratio and the alphabet remain
parameters throughout the projection, cut selection and final-output bound. -/

namespace MainIncidence

open scoped BigOperators

variable {V P C X I A R S K T : Type*}

section Projection

variable [Fintype V] [Nonempty V] [Fintype P] [Fintype C] [DecidableEq C]
variable [Fintype X] [DecidableEq X] [Nonempty X]

/-- A numerical incidence-cell cap implies a bound on the law of one marked
incidence per pin after projection through any equal-size fibers. -/
theorem project_marked_incidence (pin : V ↪ P) (cell : P → C)
    (cap : ℕ) (hports : 2 * Fintype.card P ≤ cap * Fintype.card V)
    (hcell : ∀ c, (SourceDensity.fiberCount cell c : ℚ) ≤
      2 * Fintype.card P / (Fintype.card C : ℚ))
    (proj : C → X) (m : ℕ) (hreg : ∀ x, SourceDensity.fiberCount proj x = m) (x : X) :
    EmpiricalCutMoments.empiricalLaw (fun v => proj (cell (pin v))) x ≤
      cap * ProductVariance.uniformWeight X := by
  letI : Nonempty C := Nonempty.map (fun v => cell (pin v)) ‹Nonempty V›
  have hc : (Fintype.card C : ℚ) = (Fintype.card X : ℚ) * m := by
    exact_mod_cast SourceDensity.regular_projection_card proj m hreg
  have hc0 : (Fintype.card C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx0 : (Fintype.card X : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hv : (0 : ℚ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos (α := V)
  have hproject :
      (SourceDensity.fiberCount (fun p => proj (cell p)) x : ℚ) ≤
      2 * Fintype.card P / (Fintype.card X : ℚ) := by
    rw [SourceDensity.fiberCount_comp, Nat.cast_sum]
    calc
      _ ≤ ∑ _c ∈ Finset.univ.filter (fun c => proj c = x),
          2 * Fintype.card P / (Fintype.card C : ℚ) :=
        Finset.sum_le_sum fun c _ => hcell c
      _ = (m : ℚ) * (2 * Fintype.card P / (Fintype.card C : ℚ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        change (SourceDensity.fiberCount proj x : ℚ) * _ = _
        rw [hreg]
      _ = _ := by
        apply (eq_div_iff hx0).2
        calc
          _ = (2 * Fintype.card P / (Fintype.card C : ℚ)) *
              (Fintype.card X * (m : ℚ)) := by ring
          _ = _ := by rw [← hc, div_mul_cancel₀ _ hc0]
  have hinj : (SourceDensity.fiberCount (fun v => proj (cell (pin v))) x : ℚ) ≤
      SourceDensity.fiberCount (fun p => proj (cell p)) x := by
    exact_mod_cast SourceDensity.fiberCount_injection pin (fun p => proj (cell p)) x
  have hp : 2 * (Fintype.card P : ℚ) ≤ cap * (Fintype.card V : ℚ) := by exact_mod_cast hports
  change (SourceDensity.fiberCount (fun v => proj (cell (pin v))) x : ℚ) / Fintype.card V ≤ _
  calc
    _ ≤ (2 * Fintype.card P / (Fintype.card X : ℚ)) / Fintype.card V :=
      (div_le_div_iff_of_pos_right hv).2 (hinj.trans hproject)
    _ = (2 * (Fintype.card P : ℚ) / Fintype.card V) *
          ProductVariance.uniformWeight X := by unfold ProductVariance.uniformWeight; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ hv).2 hp) (by
      unfold ProductVariance.uniformWeight
      positivity)

end Projection

section Words

variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

private def secondFiberEquiv (x : I → A) :
    {c : (I → A) × (I → A) // c.2 = x} ≃ (I → A) where
  toFun c := c.1.1
  invFun a := ⟨(a,x), rfl⟩
  left_inv := by rintro ⟨⟨a,b⟩,h⟩; cases h; rfl
  right_inv _ := rfl

omit [Nonempty A] in
theorem factor_word_fiber (x : I → A) :
    SourceDensity.fiberCount (fun c : (I → A) × (I → A) => c.2) x =
      Fintype.card (I → A) := by
  classical
  rw [SourceDensity.fiberCount, ← Fintype.card_subtype]
  exact Fintype.card_congr (secondFiberEquiv x)

private def swapFiberEquiv (i : I) (a : A) :
    {c : (I → A) × (I → A) // c.2 i = a} ≃
      {c : (I → A) × (I → A) // c.1 i = a} where
  toFun c := ⟨c.1.swap, c.2⟩
  invFun c := ⟨c.1.swap, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nonempty A] in
theorem factor_symbol_fiber (i : I) (a : A) :
    SourceDensity.fiberCount (fun c : (I → A) × (I → A) => c.2 i) a =
      (Fintype.card A) ^ (Fintype.card I - 1) * (Fintype.card A) ^ Fintype.card I := by
  classical
  rw [← BalancedUnion.single_coordinate_fiber i a]
  simp only [SourceDensity.fiberCount, ← Fintype.card_subtype]
  exact Fintype.card_congr (swapFiberEquiv i a)

end Words

variable [Fintype V] [Nonempty V] [DecidableEq V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- An actual main incidence layout together with geometric graph data.
The cell has assignment word first and coefficient-bearing factor word second.
No density, balanced union, matching, or target rank is supplied. -/
structure Layout (E : Finset (V × V)) (pin : V ↪ P)
    (cell : P → (I → A) × (I → A)) (cap : ℕ) where
  positive : 0 < cap
  ports : 2 * Fintype.card P ≤ cap * Fintype.card V
  maxLoad : ∀ c, (SourceDensity.fiberCount cell c : ℚ) ≤
    2 * Fintype.card P / (Fintype.card ((I → A) × (I → A)) : ℚ)
  alphabet : 4 * cap ≤ 3 * Fintype.card A
  loopless : ∀ v, (v, v) ∉ E
  regular : ∀ v, GraphCutMoments.degree E v = 3
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_le_one : gamma ≤ 1
  expansion : ∀ U : Finset V,
    gamma * (min U.card (Fintype.card V - U.card) : ℕ) ≤
      ((GraphCutMoments.boundary E U).card : ℚ)

variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {cap : ℕ}

def labels (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (v : V) : I → A :=
  (cell (pin v)).2

omit [Nonempty I] in
theorem Layout.density (G : Layout E pin cell cap) (x : I → A) :
    EmpiricalCutMoments.empiricalLaw (labels pin cell) x ≤
      cap * ProductVariance.uniformWeight (I → A) :=
  project_marked_incidence pin cell cap G.ports G.maxLoad
    (fun c => c.2) _ factor_word_fiber x

omit [Nonempty I] in
theorem Layout.balanced (G : Layout E pin cell cap) :
    ∃ symbols : I → Finset A, ∀ i, (1 / 4 : ℚ) * Fintype.card V ≤
      (min (EmpiricalCutMoments.labelCut (labels pin cell) id symbols i).card
        (Fintype.card V - (EmpiricalCutMoments.labelCut (labels pin cell) id symbols i).card) : ℕ) := by
  have hc : (cap : ℚ) * ProductVariance.uniformWeight A ≤ 3 / 4 := by
    have ha : 4 * (cap : ℚ) ≤ 3 * (Fintype.card A : ℚ) := by exact_mod_cast G.alphabet
    have hp : (0 : ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
    rw [ProductVariance.uniformWeight, ← div_eq_mul_inv, div_le_iff₀ hp]
    linarith only [ha]
  have hs (i : I) (a : A) :
      EmpiricalCutMoments.empiricalLaw (fun v => labels pin cell v i) a ≤ 3 / 4 :=
    (project_marked_incidence pin cell cap G.ports G.maxLoad
      (fun c => c.2 i) _ (factor_symbol_fiber i) a).trans hc
  choose symbols hsymbols using fun i => BalancedUnion.exists_balanced_vertex_union_of_law _ (hs i)
  exact ⟨symbols, hsymbols⟩

/-- Integer rounding of the scale for one balanced cut per node. -/
def scale (cap q : ℕ) : ℚ := FiniteGrowth.integerScale (cap*q)

theorem scale_bounds (cap q : ℕ) (hc : 0 < cap) (hq : 0 < q) :
    1 ≤ scale cap q ∧ (cap : ℚ)*q ≤ scale cap q ^ 2 ∧
      scale cap q ^ 2 ≤ 4*(cap : ℚ)*q := by
  obtain ⟨h₁,h₂,h₃⟩ := FiniteGrowth.integerScale_bounds (cap*q) (Nat.mul_pos hc hq)
  unfold scale
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast h₁
  · exact_mod_cast h₂
  · rw [mul_assoc]
    exact_mod_cast h₃

noncomputable def Layout.symbols (G : Layout E pin cell cap) : I → Finset A :=
  Classical.choose G.balanced

noncomputable def Layout.geometry (G : Layout E pin cell cap) :
    ExpanderBarrier.LabelGeometry E (labels pin cell) id G.symbols where
  loopless := G.loopless
  regular := G.regular
  densityConstant := cap
  gamma := G.gamma
  eta := 1 / 4
  H := scale cap (Fintype.card I)
  density_nonneg := Nat.cast_nonneg _
  density := G.density
  gamma_pos := G.gamma_pos
  gamma_le_one := G.gamma_le_one
  eta_pos := by norm_num
  eta_le_half := by norm_num
  H_ge_one := (scale_bounds _ _ G.positive Fintype.card_pos).1
  expansion := G.expansion
  balance := Classical.choose_spec G.balanced
  scale := by
    have hc (i : I) : ProductVariance.coordinateCount (id : I → I) i = 1 := by
      change (Finset.univ.filter fun j : I => j = i).card = 1
      have hf : (Finset.univ.filter fun j : I => j = i) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hf, Finset.card_singleton]
    simpa only [hc, Nat.cast_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using
      (scale_bounds cap (Fintype.card I) G.positive Fintype.card_pos).2.1

variable [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- An explicit finite main-output budget for one selected cut at each node. The scale of the
exponent uses the actual number of nodes, rather than a generic logarithmic
upper bound for that number. -/
theorem main_modular_cut_barrier (G : Layout E pin cell cap)
    (hsize : 7776 * (Fintype.card I : ℚ) * (4 * cap * (Fintype.card I : ℚ)) /
      (FiniteGrowth.coefficient G.gamma (1/4)) ^ 2 < Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → I)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut (labels pin cell) id G.symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ i, (terms i).value σ)
    (hcorrect : ∀ σ, residue (output σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4) * Fintype.card V) ^ 2 ≤
      16 * (cap : ℚ) * (Fintype.card I : ℚ) * (d : ℚ)^2 ∧ 2^d ≤ Fintype.card T := by
  classical
  let geom := G.geometry
  have hscale : geom.H ^ 2 ≤ 4 * (cap : ℚ) * (Fintype.card I : ℚ) :=
    (scale_bounds cap (Fintype.card I) G.positive Fintype.card_pos).2.2
  have hsz : 7776 * (Fintype.card I : ℚ) * geom.H ^ 2 /
      (FiniteGrowth.coefficient geom.gamma geom.eta) ^ 2 < Fintype.card V := by
    apply lt_of_le_of_lt _ hsize
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by positivity)) (sq_nonneg _)
  obtain ⟨hl, ht⟩ := FiniteGrowth.modular_growth_barrier geom hsz embed residue hinjective
    output terms assigned hside hrepresentation hcorrect
  refine ⟨⌊ExpanderBarrier.margin geom⌋₊, ?_, ht⟩
  have hh := LogarithmicBudget.squared_exponent (Fintype.card V)
    (FiniteGrowth.coefficient geom.gamma geom.eta) geom.H (4 * cap) (Fintype.card I) _
    (Nat.cast_nonneg _) (FiniteGrowth.coefficient_pos geom.gamma_pos geom.eta_pos).le
    (zero_lt_one.trans_le geom.H_ge_one) (Nat.cast_nonneg _) hscale hl
  change (FiniteGrowth.coefficient G.gamma (1/4) * Fintype.card V) ^ 2 ≤ _ at hh
  convert hh using 1
  ring

/-- An explicit finite main-output group-product budget. The scale of the
exponent uses the actual number of nodes, rather than a generic logarithmic
upper bound for that number. -/
theorem main_modular_group_barrier (G : Layout E pin cell cap)
    (hsize : 7776 * (Fintype.card I : ℚ) * (4 * cap * (Fintype.card I : ℚ)) /
      (FiniteGrowth.coefficient G.gamma (1/4)) ^ 2 < Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (labels pin cell) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ i, (terms i).value σ)
    (hcorrect : ∀ σ, residue (output σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1/4) * Fintype.card V) ^ 2 ≤
      16 * (cap : ℚ) * (Fintype.card I : ℚ) * (d : ℚ)^2 ∧ 2^d ≤ Fintype.card T := by
  classical
  exact main_modular_cut_barrier G hsize embed residue hinjective output
    (fun t => (terms t).toVertexTerm G.symbols) (fun t => (terms t).coordinate)
    (fun t => (terms t).toVertexTerm_side _)
    (fun σ => (hrepresentation σ).trans (GroupProducts.sum_toVertexTerm_values _ _ _).symm)
    hcorrect

/-- The Tovey clone family has twelve main incidences per varied unary sign. -/
theorem cloned_port_budget (nPins nInc : ℕ) (h : nInc = 12 * nPins) :
    2 * nInc ≤ 24 * nPins := by omega

#print axioms project_marked_incidence
#print axioms factor_word_fiber
#print axioms factor_symbol_fiber
#print axioms Layout.density
#print axioms Layout.balanced
#print axioms scale_bounds
#print axioms Layout.geometry
#print axioms main_modular_cut_barrier
#print axioms main_modular_group_barrier
#print axioms cloned_port_budget

end MainIncidence
