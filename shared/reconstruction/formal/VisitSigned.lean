import VisitRuntime

namespace Reconstruction.VisitRuntime

open ExpansionGraph (CNF HasBalancedCuts Satisfies)
open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The first and second polarities apply to the two endpoints in the graph's
clause order. Both can be chosen independently for every edge. -/
def signedGraphClause (G : SimpleGraph V) (e : G.edgeSet) (signs : Bool × Bool) : List (V × Bool) :=
  [((ExpansionGraph.endpoints G e).1, signs.1), ((ExpansionGraph.endpoints G e).2, signs.2)]

def signedGraphCNF (G : SimpleGraph V) [DecidableRel G.Adj] (signs : G.edgeSet → Bool × Bool) : CNF V :=
  (Finset.univ : Finset G.edgeSet).toList.map (fun e => signedGraphClause G e (signs e))

omit [DecidableEq V] in
theorem signedGraphCNF_length (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) :
    (ExpansionGraph.positiveGraphCNF G).length = (signedGraphCNF G signs).length := by
  simp [ExpansionGraph.positiveGraphCNF, signedGraphCNF]

omit [DecidableEq V] in
theorem signedGraphCNF_literalVariables (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) :
    (signedGraphCNF G signs).map (List.map Prod.fst) =
      (ExpansionGraph.positiveGraphCNF G).map (List.map Prod.fst) := by
  simp [signedGraphCNF, ExpansionGraph.positiveGraphCNF, signedGraphClause, Function.comp_def]

theorem signedGraphCNF_occurs (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) (v : V) :
    ExpansionGraph.occurs v (signedGraphCNF G signs) = G.degree v := by
  have count (F : CNF V) : ExpansionGraph.occurs v F =
      ((F.map (List.map Prod.fst)).map (fun C => (C.filter (fun u => decide (u = v))).length)).sum := by
    simp [ExpansionGraph.occurs, List.map_map, List.filter_map, Function.comp_def]
  rw [count, signedGraphCNF_literalVariables, ← count, positiveGraph_occurrences]

omit [DecidableEq V] in
/-- Exact independent-incidence degree for every signing, including an empty
edge set. Each edge contributes one binary clause. -/
theorem degree_signedGraph_product (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) :
    (binaryIncidenceProduct signs).totalDegree = 2*(signedGraphCNF G signs).length ∧
      (binaryIncidenceProduct signs).totalDegree = 2*Fintype.card G.edgeSet := by
  refine ⟨?_, degree_binaryIncidenceProduct signs⟩
  simpa [signedGraphCNF] using degree_binaryIncidenceProduct signs

omit [DecidableEq V] in
/-- Changing polarities preserves each ordered clause's physical variable
scope. The cast just identifies the two clause index types. -/
theorem signedGraphCNF_scope (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) (i : Fin (ExpansionGraph.positiveGraphCNF G).length) (v : V) :
    formulaScope (signedGraphCNF G signs) (i.cast (signedGraphCNF_length G signs)) v ↔
      formulaScope (ExpansionGraph.positiveGraphCNF G) i v := by
  have same (F : CNF V) (j : Fin F.length) : formulaScope F j v ↔ v ∈ (F.get j).map Prod.fst := by
    simp only [formulaScope, List.mem_map]
  rw [same, same]
  have h := congrArg (fun F : List (List V) => F[i.val]?) (signedGraphCNF_literalVariables G signs)
  dsimp only at h
  rw [List.getElem?_map, List.getElem?_map] at h
  have hp : (ExpansionGraph.positiveGraphCNF G)[i.val]? = some ((ExpansionGraph.positiveGraphCNF G).get i) :=
    List.getElem?_eq_getElem i.isLt
  have hs : (signedGraphCNF G signs)[i.val]? =
      some ((signedGraphCNF G signs).get (i.cast (signedGraphCNF_length G signs))) :=
    List.getElem?_eq_getElem (i.cast (signedGraphCNF_length G signs)).isLt
  rw [hp, hs, Option.map_some, Option.map_some, Option.some.injEq] at h
  rw [h]

omit [DecidableEq V] in
theorem satisfies_signedGraphCNF_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) (x : V → Bool) :
    Satisfies (signedGraphCNF G signs) x ↔
      ∀ e : G.edgeSet, x (ExpansionGraph.endpoints G e).1 = (signs e).1 ∨
        x (ExpansionGraph.endpoints G e).2 = (signs e).2 := by
  constructor
  · intro hx e
    have h := hx _ (List.mem_map.mpr ⟨e, by simp, rfl⟩)
    simpa [signedGraphClause] using h
  · intro hx C hC
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hC
    simpa [signedGraphClause] using hx e

def incidenceBitValue (b : Bool) : ℚ := if b then 1 else 0

theorem eval_binaryClauseIndicator_bool {E : Type*} (x : E × Bool → Bool) (e : E) (a b : Bool) :
    MvPolynomial.eval (fun i => incidenceBitValue (x i)) (binaryClauseIndicator e a b) =
      if x (e,false) = a ∨ x (e,true) = b then 1 else 0 := by
  cases h₁ : x (e,false) <;> cases h₂ : x (e,true) <;> cases a <;> cases b <;>
    norm_num [binaryClauseIndicator, signedIncidence, incidenceBitValue, h₁, h₂]

omit [DecidableEq V] in
/-- After Boolean inputs are read at the endpoints, the independent-incidence
product evaluates to the indicator of the signed graph formula. -/
theorem eval_signedGraph_product (G : SimpleGraph V) [DecidableRel G.Adj]
    (signs : G.edgeSet → Bool × Bool) (x : V → Bool) :
    MvPolynomial.eval (fun i : G.edgeSet × Bool => incidenceBitValue
      (if i.2 then x (ExpansionGraph.endpoints G i.1).2 else x (ExpansionGraph.endpoints G i.1).1))
      (binaryIncidenceProduct signs) =
        (by classical exact if Satisfies (signedGraphCNF G signs) x then (1:ℚ) else 0) := by
  classical
  rw [satisfies_signedGraphCNF_iff, binaryIncidenceProduct, map_prod]
  simp_rw [eval_binaryClauseIndicator_bool, Bool.false_eq_true, if_false, if_true]
  by_cases h : ∀ e : G.edgeSet, x (ExpansionGraph.endpoints G e).1 = (signs e).1 ∨
      x (ExpansionGraph.endpoints G e).2 = (signs e).2
  · simp [h]
  · obtain ⟨e, he⟩ := not_forall.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)

private def reindexFactors {F F' : Type*} {Q r R : ℕ} (L : PhysicalLayout V F Q r R)
    (i : F' → F) : PhysicalLayout V F' Q r R where
  node := L.node
  nodes_injective := L.nodes_injective
  nodes_ne_zero := L.nodes_ne_zero
  source := L.source
  target := fun t f => L.target t (i f)
  scope := fun f => L.scope (i f)
  rows := L.rows
  measure := L.measure
  poly := fun f => L.poly (i f)
  constant := fun f => L.constant (i f)
  degree := fun f => L.degree (i f)
  foreign := fun t f => L.foreign t (i f)

private def reindexVisits {F F' : Type*} {Q r R d₀ T : ℕ} {L : PhysicalLayout V F Q r R}
    (W : Visits L d₀ T) (i : F' → F) : Visits (reindexFactors L i) d₀ T where
  measurement := W.measurement
  taylorNode := W.taylorNode
  taylor := W.taylor
  scanNode := W.scanNode
  scanGroup := W.scanGroup
  largest := W.largest
  scan := W.scan

/-- Theorems 3 and 6 and the unbalanced variant hold uniformly over the
literal signs. The transport preserves the physical measurements and visits. -/
theorem theorems3_and6_signed_graphs {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) :
    ∃ C₃ C₆ Cᵤ : ℝ, 0 < C₃ ∧ 0 < C₆ ∧ 0 < Cᵤ ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) → HasBalancedCuts G →
        ∀ (signs : G.edgeSet → Bool × Bool) {Q r R d₀ T : ℕ}
          (L : PhysicalLayout (Fin n) (Fin (signedGraphCNF G signs).length) Q r R)
          (_W : Visits L d₀ T), L.scope = formulaScope (signedGraphCNF G signs) →
          c₀*(n:ℝ) ≤ d₀ →
          (L.balanced → (2:ℝ)^(C₃*arbitraryNodeScale n) ≤ T) ∧
          (L.balanced → (r:ℝ)^(2*Q) ≤ (n:ℝ)^A → C₆*((n:ℝ)*scheduledRate n) ≤ Real.log T) ∧
          (ScansAtEveryNode L T → (2:ℝ)^(Cᵤ*arbitraryNodeScale n) ≤ T) := by
  obtain ⟨C₃,C₆,Cᵤ,h₃,h₆,hᵤ,n₀,h⟩ := theorems3_and6_of_expanding_graphs hA hc₀
  refine ⟨C₃,C₆,Cᵤ,h₃,h₆,hᵤ,n₀,?_⟩
  intro n hn G _ hdeg hcuts signs Q r R d₀ T L W hscope hd₀
  let i (f : Fin (ExpansionGraph.positiveGraphCNF G).length) := f.cast (signedGraphCNF_length G signs)
  have hs : (reindexFactors L i).scope = formulaScope (ExpansionGraph.positiveGraphCNF G) := by
    funext f v
    change L.scope (i f) v = _
    rw [hscope]
    exact propext (signedGraphCNF_scope G signs f v)
  exact (h n hn G hdeg hcuts).2.2 (reindexFactors L i) (reindexVisits W i) hs hd₀

end

end Reconstruction.VisitRuntime
