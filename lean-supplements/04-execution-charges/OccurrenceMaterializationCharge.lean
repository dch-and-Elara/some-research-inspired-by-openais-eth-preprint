import RetunedLayout
import IndexedExecutionCharge

/-! Corollary 3 with independent charges at each position of the published
complete-materialization trace. Identical tags need not have identical charges. -/

namespace FixedSchedule

open scoped BigOperators

/-- An actual list of covered occurrence positions, carrying a charge at
each position. An untagged position is permitted and is still charged. -/
structure OccurrenceExecution (T : Type*) where
  trace : List (Option T)
  covers : ∀ t, some t ∈ trace
  charge : Fin trace.length → ℕ
  charge_pos : ∀ i, 1 ≤ charge i

def OccurrenceExecution.cost {T : Type*} (run : OccurrenceExecution T) : ℕ :=
  ∑ i, run.charge i

theorem card_le_occurrence_cost {T : Type*} [Fintype T]
    (run : OccurrenceExecution T) : Fintype.card T ≤ run.cost := by
  let unpriced : Execution T :=
    ⟨run.trace, run.covers, fun _ => 1, fun _ _ => le_refl 1⟩
  have hlen : Fintype.card T ≤ run.trace.length := card_le_trace_length unpriced
  exact hlen.trans (RootSeparation.IndexedExecutionCharge.embedded_count_le_charge
    run.charge id Function.injective_id run.charge_pos)

#print axioms card_le_occurrence_cost

end FixedSchedule

namespace RetunedLayout

open scoped BigOperators

variable {V P I A T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}

/-- Both D1 inequalities and the occurrence-dependent charge bound hold
for the same exponent. -/
theorem materialization_occurrence_cost (G : FullGroupBarrier.Layout E pin cell kept)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 0 ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : FixedSchedule.OccurrenceExecution T) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * ((Fintype.card V).log2 : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T ∧ 2 ^ d ≤ run.cost := by
  obtain ⟨d, hsq, hterms⟩ := modular_output_barrier G hN embed residue hinjective output
    terms hrepresentation hcorrect
  exact ⟨d, hsq, hterms, hterms.trans (FixedSchedule.card_le_occurrence_cost run)⟩

/-- At the original extra cutoff, both the representation length and the
occurrence-dependent total charge exceed the given polynomial power. -/
theorem superpolynomial_occurrence_cost (G : FullGroupBarrier.Layout E pin cell kept)
    (p : ℕ)
    (hN : max
      (LogarithmicBudget.cutoff
        (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 0)
      (PowerCost.threshold (FiniteGrowth.coefficient G.gamma (1 / 4)) p) ≤ Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : FixedSchedule.OccurrenceExecution T) :
    (Fintype.card V) ^ p < Fintype.card T ∧ (Fintype.card V) ^ p < run.cost := by
  have h := superpolynomial_representation G p hN embed residue hinjective output terms
    hrepresentation hcorrect
  exact ⟨h, h.trans_le (FixedSchedule.card_le_occurrence_cost run)⟩

#print axioms materialization_occurrence_cost
#print axioms superpolynomial_occurrence_cost

end RetunedLayout
