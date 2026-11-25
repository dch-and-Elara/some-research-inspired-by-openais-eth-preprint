import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset

namespace Reconstruction.ExpansionGraph

open Finset
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One ordered representative per undirected edge crossing the cut.
The first vertex belongs to the indicated side. -/
def crossingEdges (G : SimpleGraph V) (B : Finset V) : Finset (V × V) := by
  classical
  exact univ.filter fun e => G.Adj e.1 e.2 ∧ e.1 ∈ B ∧ e.2 ∉ B

@[simp] theorem mem_crossingEdges {G : SimpleGraph V} {B : Finset V} {u v : V} :
    (u,v) ∈ crossingEdges G B ↔ G.Adj u v ∧ u ∈ B ∧ v ∉ B := by
  classical
  simp [crossingEdges]

/-- The balanced-cut lower bound in Lemma A.1, with κ = 1/32768. -/
def HasBalancedCuts (G : SimpleGraph V) : Prop :=
  ∀ B : Finset V, Fintype.card V ≤ 4 * B.card → 2 * B.card ≤ Fintype.card V →
    Fintype.card V ≤ 32768 * (crossingEdges G B).card

/-- Partition a finite set by a decidable predicate. -/
theorem card_filter_partition {X : Type*} (s : Finset X) (p : X → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  classical
  have hu : s.filter p ∪ (s.filter fun x => ¬ p x) = s := by
    ext x
    by_cases h : p x <;> simp [h]
  have hd : Disjoint (s.filter p) (s.filter fun x => ¬ p x) := by
    apply disjoint_left.mpr
    intro x h₁ h₂
    exact (mem_filter.mp h₂).2 (mem_filter.mp h₁).2
  rw [← card_union_of_disjoint hd, hu]

section Groups

variable {L : Type*} [Fintype L] [DecidableEq L]

def groupFiber (a : V → L) (g : L) : Finset V := univ.filter fun v => a v = g

def groupUnion (a : V → L) (S : Finset L) : Finset V := univ.filter fun v => a v ∈ S

omit [DecidableEq V] [Fintype L] in
private theorem groupUnion_card (a : V → L) (S : Finset L) :
    (groupUnion a S).card = ∑ g ∈ S, (groupFiber a g).card := by
  exact (sum_card_fiberwise_eq_card_filter univ S a).symm

omit [DecidableEq V] in
/-- A balanced union exists when no individual source group exceeds half
the original-variable count. -/
theorem exists_balanced_group_union (a : V → L) (hn : 0 < Fintype.card V)
    (hgroup : ∀ g, 2 * (groupFiber a g).card ≤ Fintype.card V) :
    ∃ S : Finset L, Fintype.card V ≤ 4 * (groupUnion a S).card ∧
      2 * (groupUnion a S).card ≤ Fintype.card V := by
  classical
  by_cases h : ∃ g, Fintype.card V ≤ 4 * (groupFiber a g).card
  · obtain ⟨g, hg⟩ := h
    exact ⟨{g}, by simpa [groupUnion, groupFiber] using hg,
      by simpa [groupUnion, groupFiber] using hgroup g⟩
  let C : Finset (Finset L) := (univ : Finset (Finset L)).filter fun S =>
    Fintype.card V ≤ 4 * (groupUnion a S).card
  have hC : C.Nonempty := ⟨univ, by simp [C, groupUnion]; omega⟩
  obtain ⟨S, hS, hmin⟩ := C.exists_min_image Finset.card hC
  have hSlo := (mem_filter.mp hS).2
  have hSne : S.Nonempty := by
    by_contra! hEmpty
    have e : S = ∅ := not_nonempty_iff_eq_empty.mp hEmpty
    simp [e, groupUnion] at hSlo
    omega
  obtain ⟨g, hg⟩ := hSne
  have hsub : ¬ Fintype.card V ≤ 4 * (groupUnion a (S.erase g)).card := by
    intro hp
    exact (not_le_of_gt (card_erase_lt_of_mem hg)) (hmin _ (mem_filter.mpr ⟨mem_univ _, hp⟩))
  have hsplit : (groupUnion a (S.erase g)).card + (groupFiber a g).card =
      (groupUnion a S).card := by
    rw [groupUnion_card, groupUnion_card, sum_erase_add _ _ hg]
  have hf := not_le.mp (fun z => h ⟨g,z⟩)
  exact ⟨S, hSlo, by omega⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each undirected graph edge indexes a clause factor. -/
def incidentFactors (v : V) : Finset G.edgeSet := univ.filter fun e => v ∈ e.val

@[simp] theorem mem_incidentFactors {v : V} {e : G.edgeSet} :
    e ∈ incidentFactors G v ↔ v ∈ e.val := by
  simp [incidentFactors]

theorem incidentFactors_card (v : V) : (incidentFactors G v).card = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree v]
  refine card_bij (fun e _ => e.val) ?_ ?_ ?_
  · intro e he
    rw [G.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr e.property,
      (mem_incidentFactors G).mp he⟩
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro e he
    rw [G.incidenceFinset_eq_filter] at he
    obtain ⟨he, hv⟩ := mem_filter.mp he
    exact ⟨⟨e, SimpleGraph.mem_edgeFinset.mp he⟩, (mem_incidentFactors G).mpr hv, rfl⟩

/-- A mismatch is an incident original variable and factor with different labels. -/
def mismatchPairs (a : V → L) (b : G.edgeSet → L) : Finset (V × G.edgeSet) :=
  univ.filter fun ve => ve.2 ∈ incidentFactors G ve.1 ∧ a ve.1 ≠ b ve.2

omit [Fintype L] in
@[simp] theorem mem_mismatchPairs {a : V → L} {b : G.edgeSet → L} {v : V} {e : G.edgeSet} :
    (v,e) ∈ mismatchPairs G a b ↔ v ∈ e.val ∧ a v ≠ b e := by
  simp [mismatchPairs]

/-- Per-node candidate-factor hypothesis for Theorems 3 and 6. -/
theorem graph_candidate_factors (hcuts : HasBalancedCuts G) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3)
    (a : V → L) (b : G.edgeSet → L) (hgroup : ∀ g, 2 * (groupFiber a g).card ≤ Fintype.card V) :
    (∀ v, (incidentFactors G v).Nonempty ∧ (incidentFactors G v).card ≤ 3) ∧
      Fintype.card V ≤ 32768 * (mismatchPairs G a b).card := by
  classical
  constructor
  · intro v
    rw [← card_pos, incidentFactors_card]
    exact ⟨by have := (hdeg v).1; omega, (hdeg v).2⟩
  obtain ⟨S, hlo, hhi⟩ := exists_balanced_group_union a hn hgroup
  let B := groupUnion a S
  have hcross := hcuts B hlo hhi
  let factor (uv : V × V) (h : uv ∈ crossingEdges G B) : G.edgeSet :=
    ⟨s(uv.1, uv.2), (mem_crossingEdges.mp h).1⟩
  have hneq (uv : V × V) (h : uv ∈ crossingEdges G B) : a uv.1 ≠ a uv.2 := by
    obtain ⟨_, h1, h2⟩ := mem_crossingEdges.mp h
    intro he
    simp only [B, groupUnion, mem_filter, mem_univ, true_and] at h1 h2
    exact h2 (he ▸ h1)
  let chooseV (uv : V × V) (h : uv ∈ crossingEdges G B) :=
    if a uv.1 = b (factor uv h) then uv.2 else uv.1
  have hc : (crossingEdges G B).card ≤ (mismatchPairs G a b).card := by
    let f (u : ↥(crossingEdges G B)) : ↥(mismatchPairs G a b) := by
      obtain ⟨uv, huv⟩ := u
      refine ⟨(chooseV uv huv, factor uv huv), ?_⟩
      rw [mem_mismatchPairs]
      change chooseV uv huv ∈ s(uv.1,uv.2) ∧ a (chooseV uv huv) ≠ b (factor uv huv)
      by_cases h : a uv.1 = b (factor uv huv)
      · exact ⟨by simpa only [chooseV, h, if_true] using Sym2.mem_mk_right uv.1 uv.2, by
          simp only [chooseV, h, if_true]
          intro h'
          exact hneq uv huv (h.trans h'.symm)⟩
      · exact ⟨by simpa only [chooseV, h, if_false] using Sym2.mem_mk_left uv.1 uv.2,
          by rw [show chooseV uv huv = uv.1 by simp only [chooseV, h, if_false]]; exact h⟩
    have hinj : Function.Injective f := by
      rintro ⟨uv, huv⟩ ⟨vw, hvw⟩ he
      apply Subtype.ext
      have hpair : s(uv.1, uv.2) = s(vw.1,vw.2) := congrArg (fun z : V × G.edgeSet => z.2.val) (congrArg Subtype.val he)
      have hs : uv.1 ∈ s(vw.1,vw.2) := hpair ▸ Sym2.mem_mk_left uv.1 uv.2
      have ht : uv.2 ∈ s(vw.1,vw.2) := hpair ▸ Sym2.mem_mk_right uv.1 uv.2
      have hu1 := (mem_crossingEdges.mp huv).2.1
      have hu2 := (mem_crossingEdges.mp huv).2.2
      have hv1 := (mem_crossingEdges.mp hvw).2.1
      have hv2 := (mem_crossingEdges.mp hvw).2.2
      apply Prod.ext
      · exact (Sym2.mem_iff.mp hs).resolve_right (fun h => hv2 (h ▸ hu1))
      · exact (Sym2.mem_iff.mp ht).resolve_left (fun h => hu2 (h ▸ hv1))
    simpa using Fintype.card_le_of_injective f hinj
  exact hcross.trans (Nat.mul_le_mul_left _ hc)

end Groups

end

end Reconstruction.ExpansionGraph
