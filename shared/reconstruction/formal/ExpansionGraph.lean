import ExpansionGraphPerm
import ExpansionGraphCycle
import ExpansionGraphCNF

namespace Reconstruction.ExpansionGraph

open Finset
open scoped BigOperators

noncomputable section

section Relabel

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) (e : W ≃ V)

omit [DecidableEq V] [DecidableEq W] in
private theorem comap_degree [DecidableRel G.Adj] [DecidableRel (G.comap e).Adj] (u : W) :
    (G.comap e).degree u = G.degree (e u) := by
  rw [← (G.comap e).card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

private theorem comap_crossing_card (B : Finset W) :
    (crossingEdges (G.comap e) B).card = (crossingEdges G (B.map e.toEmbedding)).card := by
  classical
  refine card_bij (fun x _ => (e x.1,e x.2)) ?_ ?_ ?_
  · intro uv h
    obtain ⟨ha, h1,h2⟩ := mem_crossingEdges.mp h
    exact mem_crossingEdges.mpr ⟨ha, by simpa using h1, by simpa using h2⟩
  · intro uv _ xy _ h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  · intro xy h
    obtain ⟨ha, h1,h2⟩ := mem_crossingEdges.mp h
    refine ⟨(e.symm xy.1,e.symm xy.2), mem_crossingEdges.mpr ⟨?_, ?_, ?_⟩, by simp⟩
    · simpa using ha
    · obtain ⟨u, hu, h⟩ := mem_map.mp h1
      simpa [← h] using hu
    · intro hv
      exact h2 (mem_map.mpr ⟨e.symm xy.2, hv, by simp⟩)

private theorem comap_balanced (h : HasBalancedCuts G) : HasBalancedCuts (G.comap e) := by
  intro B hlo hhi
  have hn := Fintype.card_congr e
  rw [comap_crossing_card, hn]
  apply h
  · simpa only [card_map, ← hn] using hlo
  · simpa only [card_map, ← hn] using hhi

end Relabel

/-- Lemma A.1 at the paper's constant, for each positive multiple of 128. -/
theorem exists_expanding_graph {n : ℕ} (hn : 0 < n) (hdiv : 128 ∣ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧ HasBalancedCuts G := by
  obtain ⟨l, hl⟩ := hdiv
  let m := 4*l
  have hm : 0 < m := by dsimp [m]; omega
  have hn' : m*32 = n := by dsimp [m]; omega
  obtain ⟨G, hDec, hd, hG⟩ := exists_permutation_graph hm
  let p := portAssignment G hd
  let H := replaceByCycles G p
  letI : DecidableRel H.Adj := Classical.decRel _
  let e : Fin n ≃ Fin m × Port :=
    (finCongr hn'.symm).trans (finProdFinEquiv.symm.trans
      (Equiv.prodCongr (Equiv.refl _) (ZMod.finEquiv 32).toEquiv))
  let H' := H.comap e
  letI : DecidableRel H'.Adj := Classical.decRel _
  refine ⟨H', inferInstance, ?_, ?_⟩
  · intro v
    rw [comap_degree H e]
    exact replacement_degree G p (e v)
  · apply comap_balanced
    apply replacement_balanced G hd p
    · rw [Fintype.card_fin]
      exact dvd_mul_right 4 _
    · simpa only [Fintype.card_fin] using hG

theorem exists_expanding_graph_of_dvd {n : ℕ} (hdiv : 128 ∣ n) :
    ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
      (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧ HasBalancedCuts G := by
  by_cases hn : 0 < n
  · exact exists_expanding_graph hn hdiv
  · have h0 : n = 0 := by omega
    subst n
    let G : SimpleGraph (Fin 0) := ⊥
    refine ⟨G, Classical.decRel _, fun v => Fin.elim0 v, ?_⟩
    intro B _ _
    simp

/-- The positive graph CNF supplies candidate factors at every node when
source groups obey the balance assumption of Theorems 3 and 6. -/
theorem candidate_factor_family {V L T : Type*} [Fintype V] [DecidableEq V]
    [Fintype L] [DecidableEq L] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcuts : HasBalancedCuts G) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3)
    (a : T → V → L) (b : T → G.edgeSet → L)
    (hgroup : ∀ t g, 2*(groupFiber (a t) g).card ≤ Fintype.card V) :
    (∀ v, (incidentFactors G v).Nonempty ∧ (incidentFactors G v).card ≤ 3) ∧
      ∀ t, Fintype.card V ≤ 32768*(mismatchPairs G (a t) (b t)).card := by
  refine ⟨?_, fun t => (graph_candidate_factors G hcuts hn hdeg (a t) (b t) (hgroup t)).2⟩
  intro v
  rw [← card_pos, incidentFactors_card]
  exact ⟨by have := (hdeg v).1; omega, (hdeg v).2⟩

theorem positive_group_balance {V : Type*} [Fintype V] {r : ℕ} (hr : 4 ≤ r)
    (a : V → Fin r) (ha : ∀ g, r * (groupFiber a g).card ≤ 2 * Fintype.card V) :
    ∀ g, 2 * (groupFiber a g).card ≤ Fintype.card V := by
  intro g
  have H := Nat.mul_le_mul_right (groupFiber a g).card hr
  have H' := ha g
  omega

theorem extension_group_balance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 3)
    {r : ℕ} (hr : 10 ≤ r) (a : GateVar G → Fin r)
    (ha : ∀ g, r * (groupFiber a g).card ≤ 2 * Fintype.card (GateVar G)) :
    ∀ g, 2 * (groupFiber (a ∘ Sum.inl) g).card ≤ Fintype.card V := by
  intro g
  have hsub : (groupFiber (a ∘ Sum.inl) g).card ≤ (groupFiber a g).card := by
    refine card_le_card_of_injOn Sum.inl ?_ ?_
    · intro v hv
      simpa [groupFiber] using hv
    · intro _ _ _ _ h
      exact Sum.inl.inj h
  have h := (Nat.mul_le_mul_right (groupFiber (a ∘ Sum.inl) g).card hr).trans
    ((Nat.mul_le_mul_left r hsub).trans (ha g))
  have hN := (gateExtension_size G hd).1
  omega

theorem exists_large_group {V : Type*} [Fintype V] {r : ℕ} (hr : 0 < r)
    (a : V → Fin r) : ∃ g, Fintype.card V ≤ r * (groupFiber a g).card := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨g, _, hmax⟩ := (univ : Finset (Fin r)).exists_max_image
    (fun g => (groupFiber a g).card) univ_nonempty
  have htotal : (∑ i : Fin r, (groupFiber a i).card) = Fintype.card V := by
    unfold groupFiber
    rw [sum_card_fiberwise_eq_card_filter univ univ a]
    simp
  refine ⟨g, ?_⟩
  calc
    _ = ∑ i : Fin r, (groupFiber a i).card := htotal.symm
    _ ≤ ∑ _i : Fin r, (groupFiber a g).card := sum_le_sum hmax
    _ = _ := by simp

/-- Candidate-factor lists for the padded original variables in a gate extension.
Each factor is the corresponding ternary defining clause, indexed by its graph edge. -/
theorem extension_candidate_factor_family {V T : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hcuts : HasBalancedCuts G) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3)
    {r : ℕ} (hr : 10 ≤ r) (a : T → GateVar G → Fin r) (b : T → G.edgeSet → Fin r)
    (ha : ∀ t g, r*(groupFiber (a t) g).card ≤ 2 * Fintype.card (GateVar G)) :
    (∀ v, (incidentFactors G v).Nonempty ∧ (incidentFactors G v).card ≤ 3) ∧
      ∀ t, Fintype.card V ≤ 32768*(mismatchPairs G (a t ∘ Sum.inl) (b t)).card :=
  candidate_factor_family G hcuts hn hdeg (fun t => a t ∘ Sum.inl) b
    (fun t => extension_group_balance G (fun v => (hdeg v).2) hr (a t) (ha t))

/-- Padding and graph existence give the parsimonious extension for every
finite variable type, with explicit size and clause bounds. -/
theorem exists_parsimonious_expanding_extension {n w : ℕ}
    (F : CNF (Fin n)) (hw : WidthAtMost F w) :
    ∃ G : SimpleGraph (PaddedVar n), ∃ _ : DecidableRel G.Adj,
      (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) ∧ HasBalancedCuts G ∧
      Nat.card (Models (gateExtension G (padCNF F))) = Nat.card (Models F) ∧
      2 * Fintype.card (GateVar G) ≤ 5 * (n + paddingCount n) ∧
      (gateExtension G (padCNF F)).length = F.length + paddingCount n + 3*Fintype.card G.edgeSet ∧
      WidthAtMost (gateExtension G (padCNF F)) (max 3 w) := by
  obtain ⟨G, hDec, hd, hcuts⟩ :=
    exists_expanding_graph_of_dvd (paddingCount_dvd n)
  let e : PaddedVar n ≃ Fin (n + paddingCount n) := finSumFinEquiv
  let G' := G.comap e
  letI : DecidableRel G'.Adj := Classical.decRel _
  have hd' (v : PaddedVar n) : 2 ≤ G'.degree v ∧ G'.degree v ≤ 3 := by
    rw [comap_degree G e]
    exact hd (e v)
  refine ⟨G', inferInstance, hd', comap_balanced G e hcuts,
    Nat.card_congr (parsimonious_extension F G').symm, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin] using
      (gateExtension_size G' (fun v => (hd' v).2)).1
  · rw [gateExtension_length, padCNF_length]
  · simpa only [← max_assoc, max_eq_left (show (1:ℕ) ≤ 3 by omega)] using
      gateExtension_width G' (padCNF_width hw)

theorem padded_gate_occurs_original {n : ℕ} (F : CNF (Fin n))
    (G : SimpleGraph (PaddedVar n)) [DecidableRel G.Adj] (v : Fin n) :
    occurs (Sum.inl (Sum.inl v)) (gateExtension G (padCNF F)) =
      occurs v F + 2 * G.degree (Sum.inl v) := by
  rw [gateExtension_occurs_old, padCNF_occurs_old]

theorem padded_gate_occurs_padding {n : ℕ} (F : CNF (Fin n))
    (G : SimpleGraph (PaddedVar n)) [DecidableRel G.Adj] (v : Fin (paddingCount n)) :
    occurs (Sum.inl (Sum.inr v)) (gateExtension G (padCNF F)) =
      1 + 2 * G.degree (Sum.inr v) := by
  rw [gateExtension_occurs_old, padCNF_occurs_new]

end

end Reconstruction.ExpansionGraph
