import SourceBarrier
import FiniteGrowth

/-! Cost in an explicitly materializing execution interface.

A trace event can materialize one term, or be an unrelated operation. The
interface requires every term of the fixed output representation to be
materialized during this trace. Every event has a positive integer charge.
The theorem does not assert that arbitrary scalar programs have such traces.
-/

namespace FixedSchedule

open scoped BigOperators

variable {T : Type*} [Fintype T]

/-- A trace for the model in which all terms of the fixed representation
are individually materialized. `none` permits arbitrary additional work. -/
structure Execution (T : Type*) where
  trace : List (Option T)
  covers : ∀ t, some t ∈ trace
  charge : Option T → ℕ
  charge_pos : ∀ event ∈ trace, 1 ≤ charge event

def Execution.cost (run : Execution T) : ℕ := (run.trace.map run.charge).sum

theorem card_le_trace_length (run : Execution T) : Fintype.card T ≤ run.trace.length := by
  classical
  have hc : (Finset.univ : Finset T).card ≤ run.trace.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun t => some t)
    · intro t _
      exact List.mem_toFinset.mpr (run.covers t)
    · intro x _ y _ hxy
      exact Option.some.inj hxy
  exact hc.trans run.trace.toFinset_card_le

private theorem length_le_charges {X : Type*} (xs : List X) (charge : X → ℕ)
    (hpos : ∀ x ∈ xs, 1 ≤ charge x) : xs.length ≤ (xs.map charge).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hx := hpos x (by simp)
    have ht := ih (fun y hy => hpos y (by simp [hy]))
    omega

theorem card_le_cost (run : Execution T) : Fintype.card T ≤ run.cost :=
  (card_le_trace_length run).trans (length_le_charges run.trace run.charge run.charge_pos)

variable {V P I A J R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}
variable {owner : J → kept} {symbols : J → Finset A}

/-- The finite source-layout barrier gives a cost bound for an actual trace
of the complete-term materialization model. The representation is fixed over
the whole pin family; this trace must cover all of its terms. -/
theorem source_output_cost (G : SourceBarrier.Geometry E pin cell kept owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ ExpanderBarrier.margin G.toLabelGeometry)
    (hbudget : ExpanderBarrier.SelectionBudget G.toLabelGeometry)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side =
      EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) owner symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : Execution T) : 2 ^ d ≤ run.cost :=
  (SourceBarrier.modular_output_barrier G d hd hbudget embed residue hinjective
    output terms assigned hside hrepresentation hcorrect).trans (card_le_cost run)

/-- An explicit floored exponent and the proportional exponent estimate,
under the single finite threshold in FiniteGrowth. -/
theorem source_growth_cost [Nonempty J]
    (G : SourceBarrier.Geometry E pin cell kept owner symbols)
    (hsize : 7776 * (Fintype.card J : ℚ) * G.H ^ 2 /
      (FiniteGrowth.coefficient G.gamma G.eta) ^ 2 < Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side =
      EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) owner symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S))
    (run : Execution T) :
    FiniteGrowth.coefficient G.gamma G.eta * Fintype.card V / (2 * G.H) ≤
      (⌊ExpanderBarrier.margin G.toLabelGeometry⌋₊ : ℚ) ∧
      2 ^ ⌊ExpanderBarrier.margin G.toLabelGeometry⌋₊ ≤ run.cost := by
  obtain ⟨hexponent, hterms⟩ := FiniteGrowth.modular_growth_barrier G.toLabelGeometry hsize
    embed residue hinjective output terms assigned hside hrepresentation hcorrect
  exact ⟨hexponent, hterms.trans (card_le_cost run)⟩

#print axioms card_le_trace_length
#print axioms card_le_cost
#print axioms source_output_cost
#print axioms source_growth_cost

end FixedSchedule
