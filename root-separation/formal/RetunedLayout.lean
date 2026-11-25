import FullGroupBarrier
import SourceCoordinates
import PowerCost

/-! The retained-coordinate logarithmic cap follows from actual nonempty
cell occupancy, without the published choice of the coordinate parameter.
Thus the full-group theorem applies to every layout satisfying its packing
certificate and port/alphabet conditions, with a uniform finite cutoff. -/

namespace RetunedLayout

open scoped BigOperators

variable {V P I A T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}

/-- No fixed coordinate schedule, balanced-cut premise, signed-moment premise,
or matrix-rank premise occurs here. The actual source layout certifies them. -/
theorem modular_output_barrier (G : FullGroupBarrier.Layout E pin cell kept)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 0 ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * ((Fintype.card V).log2 : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T := by
  have hcoords := SourceCoordinates.kept_card_le_log pin cell G.delta G.certificate
    G.ports G.alphabet kept G.kept_nonempty
  simpa only [Nat.add_zero] using FullGroupBarrier.logarithmic_modular_barrier G 0
    hcoords hN embed residue hinjective output terms hrepresentation hcorrect

/-- The same bound on a complete-term materialization trace. Altering the
coordinate count within the certified layout class cannot remove it. -/
theorem materialization_cost (G : FullGroupBarrier.Layout E pin cell kept)
    (hN : LogarithmicBudget.cutoff
      (LogarithmicBudget.multiplier 1 80 (FiniteGrowth.coefficient G.gamma (1 / 4))) 0 ≤
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R)
    (terms : T → GroupProducts.GroupTerm (SourceBarrier.labels pin cell kept) K)
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : FixedSchedule.Execution T) :
    ∃ d : ℕ, (FiniteGrowth.coefficient G.gamma (1 / 4) * Fintype.card V) ^ 2 ≤
      320 * ((Fintype.card V).log2 : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ run.cost := by
  obtain ⟨d, hsq, hterms⟩ := modular_output_barrier G hN embed residue hinjective output
    terms hrepresentation hcorrect
  exact ⟨d, hsq, hterms.trans (FixedSchedule.card_le_cost run)⟩

/-- For each fixed polynomial degree, every such representation is larger
than that power of N beyond the displayed finite threshold. -/
theorem superpolynomial_representation (G : FullGroupBarrier.Layout E pin cell kept)
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
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    (Fintype.card V) ^ p < Fintype.card T := by
  apply PowerCost.polynomial_lt_cost (FiniteGrowth.coefficient G.gamma (1 / 4))
    (Fintype.card V) (Fintype.card T) p
    (FiniteGrowth.coefficient_pos G.gamma_pos (by norm_num))
    ((le_max_right _ _).trans hN)
  exact modular_output_barrier G ((le_max_left _ _).trans hN) embed residue hinjective
    output terms hrepresentation hcorrect

/-- A formal superpolynomial obstruction for the complete-term materializing
model. There is deliberately no assertion that arbitrary programs implement
this model, or that other methods for SAT must have this cost. -/
theorem superpolynomial_cost (G : FullGroupBarrier.Layout E pin cell kept)
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
    (run : FixedSchedule.Execution T) : (Fintype.card V) ^ p < run.cost :=
  (superpolynomial_representation G p hN embed residue hinjective output terms
    hrepresentation hcorrect).trans_le (FixedSchedule.card_le_cost run)

#print axioms modular_output_barrier
#print axioms materialization_cost
#print axioms superpolynomial_representation
#print axioms superpolynomial_cost

end RetunedLayout
