import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Option
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Section6

open scoped BigOperators
open Finset
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual Taylor pairs, with no identifications between different supports. -/
abbrev TaylorPair (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :=
  {p : Finset V × Finset V // p.1.card ≤ q ∧ p.2 ⊆ p.1}

lemma taylor_ge_choose (q j : ℕ) (hj : j ≤ q) :
    (Fintype.card V).choose j ≤ Fintype.card (TaylorPair V q) := by
  let f : {E : Finset V // E ∈ (univ : Finset V).powersetCard j} → TaylorPair V q :=
    fun E => ⟨(E, ∅), (mem_powersetCard.mp E.property).2.le.trans hj, empty_subset _⟩
  have h := Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun p : TaylorPair V q => p.val.1) h))
  simpa [Fintype.card_coe, card_powersetCard] using h

lemma taylor_ge_two_pow (q : ℕ) :
    2 ^ min q (Fintype.card V) ≤ Fintype.card (TaylorPair V q) := by
  obtain ⟨E, _, hcard⟩ := exists_subset_card_eq
    (show min q (Fintype.card V) ≤ (univ : Finset V).card by simp)
  let f : {U : Finset V // U ∈ E.powerset} → TaylorPair V q :=
    fun U => ⟨(E, U), hcard.trans_le (min_le_left _ _), mem_powerset.mp U.property⟩
  have h := Fintype.card_le_of_injective f (fun a b h =>
    Subtype.ext (congrArg (fun p : TaylorPair V q => p.val.2) h))
  rw [Fintype.card_coe, card_powerset, hcard] at h
  exact h

lemma largest_group_ge_average {G : Type*} [Fintype G] [Nonempty G] [DecidableEq G]
    (group : V → G) :
    ∃ g, Fintype.card V ≤ Fintype.card G * (univ.filter fun v => group v = g).card := by
  classical
  obtain ⟨g, _, hg⟩ := exists_max_image (univ : Finset G)
    (fun g => (univ.filter fun v => group v = g).card) univ_nonempty
  refine ⟨g, ?_⟩
  calc
    Fintype.card V = ∑ i : G, (univ.filter fun v => group v = i).card := by
      simpa using (card_eq_sum_card_fiberwise (s := (univ : Finset V))
        (t := (univ : Finset G)) (f := group) (fun _ _ => mem_univ _))
    _ ≤ ∑ _ : G, (univ.filter fun v => group v = g).card :=
      sum_le_sum fun i hi => hg i hi
    _ = _ := by simp

/-- Any local assignment extends by false outside its group. In particular the
extension has a realized summary, with no fixed-one bits at the empty Taylor pair. -/
theorem empty_pair_local_extends {G Y : Type*} [DecidableEq G] (group : V → G)
    (summary : (V → Bool) → Y) (g : G) (u : {v // group v = g} → Bool) :
    ∃ y ∈ Set.range summary, ∃ x : V → Bool, summary x = y ∧
      ∀ v : {v // group v = g}, x v = u v := by
  let x (v : V) : Bool := if hv : group v = g then u ⟨v, hv⟩ else false
  exact ⟨summary x, ⟨x, rfl⟩, x, rfl, fun v => dif_pos v.property⟩

/-- Each lower bound has its own injection into operation indices. The operations
may overlap across layers and the group and summary may be at different nodes. -/
structure Visits (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ)
    (Y Local : Type*) (T : ℕ) where
  taylor : TaylorPair V q ↪ Fin T
  summary : Y ↪ Fin T
  localScan : Local ↪ Fin T

theorem visit_counts {V Y Local : Type*} [Fintype V] [DecidableEq V]
    [Fintype Y] [Fintype Local] {q T : ℕ} (vis : Visits V q Y Local T) :
    Fintype.card (TaylorPair V q) ≤ T ∧ Fintype.card Y ≤ T ∧ Fintype.card Local ≤ T := by
  exact ⟨by simpa using Fintype.card_le_of_injective _ vis.taylor.injective,
    by simpa using Fintype.card_le_of_injective _ vis.summary.injective,
    by simpa using Fintype.card_le_of_injective _ vis.localScan.injective⟩

/-- Polynomial multiplier accounted for separately in the source. The literal
grid scans both representatives and group fibers, hence the factor two. -/
def scanBound (Q r pairs D rows maxGroup : ℕ) : ℕ :=
  2 * Q * r * pairs * (2 * D + 1) ^ rows * 2 ^ maxGroup

#print axioms taylor_ge_choose
#print axioms taylor_ge_two_pow
#print axioms largest_group_ge_average
#print axioms empty_pair_local_extends
#print axioms visit_counts

end Section6


