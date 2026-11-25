import GroupProducts
import FixedSchedule
import LogarithmicBudget

/-! A source-layout barrier for actual products over all symbol groups.

The input does not supply balanced cuts, a moment estimate, a common matching,
a rank hypothesis, or a separated-factor rewrite. All of those are derived
from the collision certificate and the typed group-local functions. The
remaining geometric assumption is expansion of the supplied cubic graph.
-/

namespace FullGroupBarrier

open scoped BigOperators

def scale (k : ℕ) : ℚ := FiniteGrowth.integerScale (20 * k)

theorem scale_bounds (k : ℕ) (hk : 0 < k) :
    1 ≤ scale k ∧ 20 * (k : ℚ) ≤ scale k ^ 2 ∧ scale k ^ 2 ≤ 80 * (k : ℚ) := by
  obtain ⟨h1, h2, h3⟩ := FiniteGrowth.integerScale_bounds (20 * k) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold scale
    exact_mod_cast h1
  · unfold scale
    exact_mod_cast h2
  · have hh : (FiniteGrowth.integerScale (20 * k) : ℚ) ^ 2 ≤ 4 * (20 * (k : ℚ)) := by
      exact_mod_cast h3
    unfold scale
    nlinarith only [hh]

variable {V P I A T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Layout and graph inputs, before choosing any cuts or rewriting any factor.
The port count and collision certificate are explicit source conditions. -/
structure Layout (E : Finset (V × V)) (pin : V ↪ P)
    (cell : P → (I → A) × (I → A)) (kept : Finset I) where
  delta : ℚ
  certificate : SourceDensity.CollisionCertificate cell delta
  ports : Fintype.card P = 10 * Fintype.card V
  loopless : ∀ v, (v, v) ∉ E
  regular : ∀ v, GraphCutMoments.degree E v = 3
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_le_one : gamma ≤ 1
  expansion : ∀ U : Finset V,
    gamma * (min U.card (Fintype.card V - U.card) : ℕ) ≤
      ((GraphCutMoments.boundary E U).card : ℚ)
  alphabet : 27 ≤ Fintype.card A
  kept_nonempty : kept.Nonempty

variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}

/-- One cut per used coordinate has multiplicity exactly one. The canonical
integer scale therefore proves the moment-scale field automatically. -/
def Layout.toGeometry (G : Layout E pin cell kept) (symbols : kept → Finset A)
    (hbalance : ∀ i, (1 / 4 : ℚ) * Fintype.card V ≤
      (min (EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) id symbols i).card
        (Fintype.card V -
          (EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) id symbols i).card) : ℕ)) :
    SourceBarrier.Geometry E pin cell kept id symbols where
  delta := G.delta
  certificate := G.certificate
  ports := G.ports
  loopless := G.loopless
  regular := G.regular
  gamma := G.gamma
  eta := 1 / 4
  H := scale kept.card
  gamma_pos := G.gamma_pos
  gamma_le_one := G.gamma_le_one
  eta_pos := by norm_num
  eta_le_half := by norm_num
  H_ge_one := (scale_bounds kept.card G.kept_nonempty.card_pos).1
  expansion := G.expansion
  balance := hbalance
  scale := by
    have hc (i : kept) : ProductVariance.coordinateCount (id : kept → kept) i = 1 := by
      change (Finset.univ.filter fun j : kept => j = i).card = 1
      have hf : (Finset.univ.filter fun j : kept => j = i) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hf, Finset.card_singleton]
    simpa only [hc, Nat.cast_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Fintype.card_coe] using
        (scale_bounds kept.card G.kept_nonempty.card_pos).2.1

variable [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- The explicit finite logarithmic bound for full group products. Cut
balance, signed moments, the common matching, and term rank are all derived. -/
theorem logarithmic_modular_barrier (G : Layout E pin cell kept)
    (a : ℕ) (hcoords : kept.card ≤ (Fintype.card V).log2 + a)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) a ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * (((Fintype.card V).log2 + a : ℕ) : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T := by
  classical
  letI : Nonempty kept := ⟨⟨G.kept_nonempty.choose, G.kept_nonempty.choose_spec⟩⟩
  obtain ⟨symbols, hbalance, hside, hvalue⟩ := GroupProducts.source_balanced_views
    pin cell G.delta G.certificate G.ports G.alphabet kept terms
  let geom := G.toGeometry symbols hbalance
  have hm : (Fintype.card kept : ℚ) ≤ 1 * (kept.card : ℚ) := by simp
  have hs : geom.toLabelGeometry.H ^ 2 ≤ 80 * (kept.card : ℚ) :=
    (scale_bounds kept.card G.kept_nonempty.card_pos).2.2
  have hrepr : ∀ σ, embed (output σ) =
      ∑ t, ((terms t).toVertexTerm symbols).value σ := by
    intro σ
    simpa only [hvalue] using hrepresentation σ
  obtain ⟨d, hsq, hterms⟩ := LogarithmicBudget.logarithmic_modular_barrier
    geom.toLabelGeometry kept.card a 1 80 (by norm_num) hm hs hcoords hN
    embed residue hinjective output (fun t => (terms t).toVertexTerm symbols)
    (fun t => (terms t).coordinate) hside hrepr hcorrect
  refine ⟨d, ?_, hterms⟩
  change (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
    4 * 80 * (((Fintype.card V).log2 + a : ℕ) : ℚ) * (d : ℚ) ^ 2 at hsq
  norm_num only [show (4 : ℚ) * 80 = 320 by norm_num] at hsq
  exact hsq

/-- The same exponent lower bound on positive charged events in a trace that
individually materializes all fixed group-product summands. -/
theorem logarithmic_materialization_cost (G : Layout E pin cell kept)
    (a : ℕ) (hcoords : kept.card ≤ (Fintype.card V).log2 + a)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) a ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : FixedSchedule.Execution T) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * (((Fintype.card V).log2 + a : ℕ) : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ run.cost := by
  obtain ⟨d, hsq, hterms⟩ := logarithmic_modular_barrier G a hcoords hN
    embed residue hinjective output terms hrepresentation hcorrect
  exact ⟨d, hsq, hterms.trans (FixedSchedule.card_le_cost run)⟩

/-- The published coordinate upper bound (including both halves a=2u)
discharges the logarithmic coordinate-count premise with additive constant 3. -/
theorem published_coordinate_cost (G : Layout E pin cell kept)
    (hcoords : kept.card ≤ 2 * LogarithmicBudget.activeCoordinates (7 * Fintype.card V / 2))
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 3 ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : FixedSchedule.Execution T) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * (((Fintype.card V).log2 + 3 : ℕ) : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ run.cost :=
  logarithmic_materialization_cost G 3
    (hcoords.trans (LogarithmicBudget.source_root_coordinates_le_log (Fintype.card V))) hN
    embed residue hinjective output terms hrepresentation hcorrect run

#print axioms scale_bounds
#print axioms Layout.toGeometry
#print axioms logarithmic_modular_barrier
#print axioms logarithmic_materialization_cost
#print axioms published_coordinate_cost

end FullGroupBarrier
