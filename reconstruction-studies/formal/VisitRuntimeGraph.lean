import VisitRuntimeAssembly
import ExpansionGraphCNF

open scoped BigOperators
open Finset Filter

namespace Reconstruction.VisitRuntime

open LayoutBudget (GroupFiber)
open ExpansionGraph (CNF HasBalancedCuts)

noncomputable section

variable {X V F : Type*} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
  {Q r R : ℕ}

/-- Interpret a formula's factor index as the index of a clause in its list. -/
def formulaScope {V : Type*} (F : CNF V) (i : Fin F.length) (v : V) : Prop :=
  ∃ l ∈ F.get i, l.1 = v

/-- The selected physical variables and their corresponding graph-edge factors. -/
structure GraphFactors (G : SimpleGraph X) (L : PhysicalLayout V F Q r R) where
  original : X ↪ V
  edge : G.edgeSet ↪ F
  incident : ∀ e v, v ∈ e.val → L.scope (edge e) (original v)

namespace GraphFactors

variable {G : SimpleGraph X} [DecidableRel G.Adj] {L : PhysicalLayout V F Q r R}
  (B : GraphFactors G L)

def originalSet : Finset V := Finset.univ.map B.original

omit [Fintype V] [DecidableEq X] [DecidableRel G.Adj] in
theorem card_originalSet : B.originalSet.card = Fintype.card X := by
  simp [originalSet]

def originalEquiv : X ≃ B.originalSet := Equiv.ofBijective
  (fun x => ⟨B.original x, Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)
  ⟨fun _ _ h => B.original.injective (congrArg Subtype.val h), fun u => by
    obtain ⟨x,_,hx⟩ := Finset.mem_map.mp u.property
    exact ⟨x, Subtype.ext hx⟩⟩

omit [DecidableEq X] [DecidableRel G.Adj] in
theorem originalFiber_le (t : Fin Q) (g : Fin r) :
    (ExpansionGraph.groupFiber (fun x => L.source t (B.original x)) g).card ≤ L.groupSize t g := by
  classical
  let e : (ExpansionGraph.groupFiber (fun x => L.source t (B.original x)) g : Finset X) ↪
      GroupFiber (L.source t) g :=
    ⟨fun x => ⟨B.original x.val, (Finset.mem_filter.mp x.property).2⟩,
      fun _ _ h => Subtype.ext (B.original.injective (congrArg Subtype.val h))⟩
  simpa only [Fintype.card_coe, PhysicalLayout.groupSize] using Fintype.card_le_of_embedding e

/-- Appendix A's crossing edges give the candidate list demand for the physical
layout, with `δ = 1/32768`, `Δ = 3`. -/
def candidates (hcuts : HasBalancedCuts G) (hn : 0 < Fintype.card X)
    (hdeg : ∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3)
    (hgroup : ∀ t g, 2*L.groupSize t g ≤ Fintype.card X) :
    CandidateFactors L B.originalSet (1/32768:ℝ) 3 := by
  classical
  let E := B.originalEquiv
  let menu (u : B.originalSet) := (ExpansionGraph.incidentFactors G (E.symm u)).map B.edge
  refine ⟨menu, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [← Finset.card_pos, Finset.card_map, ExpansionGraph.incidentFactors_card]
    exact lt_of_lt_of_le (by decide) (hdeg (E.symm u)).1
  · intro u
    rw [Finset.card_map, ExpansionGraph.incidentFactors_card]
    exact (hdeg (E.symm u)).2
  · intro u f hf
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hf
    have hi := B.incident e (E.symm u) ((ExpansionGraph.mem_incidentFactors G).mp he)
    have hu : B.original (E.symm u) = u.val := congrArg Subtype.val (E.apply_symm_apply u)
    rwa [hu] at hi
  · intro t
    let a (x : X) := L.source t (B.original x)
    let b (e : G.edgeSet) := L.target t (B.edge e)
    have hd := (ExpansionGraph.graph_candidate_factors G hcuts hn hdeg a b
      (fun g => (Nat.mul_le_mul_left 2 (B.originalFiber_le t g)).trans (hgroup t g))).2
    have hd' : (Fintype.card X:ℝ) ≤ 32768*((ExpansionGraph.mismatchPairs G a b).card:ℝ) := by exact_mod_cast hd
    have hcard : ((ExpansionGraph.mismatchPairs G a b).card:ℝ) =
        ∑ x : X, ∑ e ∈ ExpansionGraph.incidentFactors G x, if a x ≠ b e then (1:ℝ) else 0 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      simp only [Nat.cast_one, ExpansionGraph.mismatchPairs, Finset.sum_filter]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      have he : (Finset.univ.filter (fun (e : G.edgeSet) =>
          e ∈ ExpansionGraph.incidentFactors G x ∧ a x ≠ b e)) =
          (ExpansionGraph.incidentFactors G x).filter (fun e => a x ≠ b e) := by
        ext
        simp
      calc
        _ = ∑ _ ∈ Finset.univ.filter (fun (e : G.edgeSet) =>
          e ∈ ExpansionGraph.incidentFactors G x ∧ a x ≠ b e), (1:ℝ) := by
            rw [Finset.sum_filter]
        _ = _ := by rw [he, Finset.sum_filter]
    rw [B.card_originalSet]
    calc
      _ ≤ ((ExpansionGraph.mismatchPairs G a b).card:ℝ) := by linarith only [hd']
      _ = _ := by
        rw [hcard]
        apply Fintype.sum_equiv E
        intro x
        simp [menu, E, a, b, originalEquiv]

end GraphFactors

private def occurrenceIndex {V : Type*} {F : CNF V} {clause : List (V × Bool)}
    (h : clause ∈ F) : Fin F.length := Classical.choose (List.mem_iff_get.mp h)

private theorem get_occurrenceIndex {V : Type*} {F : CNF V} {clause : List (V × Bool)}
    (h : clause ∈ F) : F.get (occurrenceIndex h) = clause :=
  Classical.choose_spec (List.mem_iff_get.mp h)

omit [Fintype X] [DecidableEq X] in
private theorem edge_mem_endpoints {G : SimpleGraph X} [DecidableRel G.Adj]
    (e : G.edgeSet) (v : X) (hv : v ∈ e.val) :
    v = (ExpansionGraph.endpoints G e).1 ∨ v = (ExpansionGraph.endpoints G e).2 := by
  rw [← ExpansionGraph.endpoints_eq G e] at hv
  rcases hp : ExpansionGraph.endpoints G e with ⟨a,b⟩
  simpa only [hp, Sym2.mem_iff] using hv

/-- The graph-edge factors of the positive 2-CNF. -/
def positiveGraphFactors (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : PhysicalLayout V (Fin (ExpansionGraph.positiveGraphCNF G).length) Q r R)
    (hscope : L.scope = formulaScope (ExpansionGraph.positiveGraphCNF G)) : GraphFactors G L := by
  classical
  let clause (e : G.edgeSet) : List (V × Bool) :=
    [((ExpansionGraph.endpoints G e).1,true),((ExpansionGraph.endpoints G e).2,true)]
  have hm (e : G.edgeSet) : clause e ∈ ExpansionGraph.positiveGraphCNF G := by
    exact List.mem_map.mpr ⟨e, by simp, rfl⟩
  let edge (e : G.edgeSet) := occurrenceIndex (hm e)
  have he (e : G.edgeSet) : (ExpansionGraph.positiveGraphCNF G).get (edge e) = clause e :=
    get_occurrenceIndex (hm e)
  refine ⟨Function.Embedding.refl V, ⟨edge, ?_⟩, ?_⟩
  · intro e f h
    have hh : clause e = clause f := by rw [← he e, ← he f, h]
    have hp : ExpansionGraph.endpoints G e = ExpansionGraph.endpoints G f := by
      simp only [clause, List.cons.injEq, Prod.mk.injEq, and_true] at hh
      exact Prod.ext hh.1 hh.2
    exact Subtype.ext (by rw [← ExpansionGraph.endpoints_eq G e, ← ExpansionGraph.endpoints_eq G f, hp])
  · intro e v hv
    rw [hscope]
    change ∃ l ∈ (ExpansionGraph.positiveGraphCNF G).get (edge e), l.1 = v
    rw [he]
    rcases edge_mem_endpoints e v hv with hv | hv
    · exact ⟨_, List.mem_cons_self .., hv.symm⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hv.symm⟩

/-- The ternary gate clause gives each original endpoint a candidate factor in
the extended formula. Original variables are included by `Sum.inl`. -/
def gateGraphFactors (G : SimpleGraph X) [DecidableRel G.Adj] (F₀ : CNF X)
    (L : PhysicalLayout (ExpansionGraph.GateVar G) (Fin (ExpansionGraph.gateExtension G F₀).length) Q r R)
    (hscope : L.scope = formulaScope (ExpansionGraph.gateExtension G F₀)) : GraphFactors G L := by
  classical
  let clause (e : G.edgeSet) : List (ExpansionGraph.GateVar G × Bool) :=
    [(Sum.inr e,true),(Sum.inl (ExpansionGraph.endpoints G e).1,false),
      (Sum.inl (ExpansionGraph.endpoints G e).2,false)]
  have hm (e : G.edgeSet) : clause e ∈ ExpansionGraph.gateExtension G F₀ := by
    apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    exact ⟨e, by simp, by simp [clause, ExpansionGraph.gateClauses]⟩
  let edge (e : G.edgeSet) := occurrenceIndex (hm e)
  have he (e : G.edgeSet) : (ExpansionGraph.gateExtension G F₀).get (edge e) = clause e :=
    get_occurrenceIndex (hm e)
  refine ⟨⟨Sum.inl, Sum.inl_injective⟩, ⟨edge, ?_⟩, ?_⟩
  · intro e f h
    have hh : clause e = clause f := by rw [← he e, ← he f, h]
    simpa only [clause, List.cons.injEq, Prod.mk.injEq, Sum.inr.injEq, and_true] using
      (List.cons.inj hh).1
  · intro e v hv
    rw [hscope]
    change ∃ l ∈ (ExpansionGraph.gateExtension G F₀).get (edge e), l.1 = Sum.inl v
    rw [he]
    rcases edge_mem_endpoints e v hv with hv | hv
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), congrArg Sum.inl hv.symm⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), congrArg Sum.inl hv.symm⟩

omit [DecidableEq V] in
/-- The factor list contains exactly one positive binary clause for each edge. -/
theorem positiveGraph_clause_shape (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ C ∈ ExpansionGraph.positiveGraphCNF G, C.length = 2 ∧ ∀ l ∈ C, l.2 = true := by
  intro C hC
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hC
  simp

theorem positiveGraph_occurrences (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    ExpansionGraph.occurs v (ExpansionGraph.positiveGraphCNF G) = G.degree v := by
  classical
  let C (e : G.edgeSet) : List (V × Bool) :=
    [((ExpansionGraph.endpoints G e).1,true),((ExpansionGraph.endpoints G e).2,true)]
  have hf (e : G.edgeSet) : ((C e).filter (fun l => decide (l.1 = v))).length = if v ∈ e.val then 1 else 0 := by
    rw [← ExpansionGraph.endpoints_eq G e]
    have hne := (ExpansionGraph.endpoints_adj G e).ne
    simp only [C, Sym2.mem_iff]
    by_cases h₁ : v = (ExpansionGraph.endpoints G e).1 <;>
      by_cases h₂ : v = (ExpansionGraph.endpoints G e).2 <;>
      simp_all [eq_comm]
  unfold ExpansionGraph.occurs ExpansionGraph.positiveGraphCNF
  rw [List.map_map, Finset.sum_map_toList]
  change (∑ e : G.edgeSet, ((C e).filter (fun l => decide (l.1 = v))).length) = _
  simp_rw [hf]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ExpansionGraph.incidentFactors_card G v

omit [DecidableEq V] in
/-- The number of independent incidence indeterminates of the positive graph
formula is twice its edge count and at least twice the number of vertices. -/
theorem positiveGraph_incidence_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) : 2*Fintype.card V ≤
    ((ExpansionGraph.positiveGraphCNF G).map List.length).sum := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdeg v)
  rw [G.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card] at hs
  unfold ExpansionGraph.positiveGraphCNF
  rw [List.map_map, Finset.sum_map_toList]
  simpa [mul_comm] using hs

/-- Candidate lists for a balanced layout when at least two fifths of the
physical variables are original. -/
theorem GraphFactors.balanced_candidates {G : SimpleGraph X} [DecidableRel G.Adj]
    {L : PhysicalLayout V F Q r R} (B : GraphFactors G L) (hcuts : HasBalancedCuts G)
    (hX : 0 < Fintype.card X) (hdeg : ∀ x, 2 ≤ G.degree x ∧ G.degree x ≤ 3)
    (hρ : (2/5:ℝ)*(Fintype.card V:ℝ) ≤ Fintype.card X) (hb : L.balanced) (hr : 10 ≤ r) :
    Nonempty (CandidateFactors L B.originalSet (1/32768:ℝ) 3) := by
  refine ⟨B.candidates hcuts hX hdeg ?_⟩
  intro t g
  have hr' : (10:ℝ) ≤ r := by exact_mod_cast hr
  have hgs : 0 ≤ (L.groupSize t g:ℝ) := by positivity
  have hprod := (le_div_iff₀ (show 0 < (r:ℝ) by linarith)).mp (hb t g)
  have hten := mul_le_mul_of_nonneg_right hr' hgs
  exact_mod_cast (show 2*(L.groupSize t g:ℝ) ≤ (Fintype.card X:ℝ) by nlinarith only [hρ,hprod,hten])

end

end Reconstruction.VisitRuntime
