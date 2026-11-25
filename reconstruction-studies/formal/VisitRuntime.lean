import VisitRuntimeGraph
import VisitRuntimeDegree
import ExpansionGraph

namespace Reconstruction.VisitRuntime

open ExpansionGraph (CNF HasBalancedCuts GateVar PaddedVar)

noncomputable section

/-- The graph formula's independent-incidence product has degree twice the
edge count, for arbitrary literal signs on the same scopes. -/
theorem graph_preSubstitution_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v, 2 ≤ G.degree v)
    (signs : G.edgeSet → Bool × Bool) :
    (binaryIncidenceProduct signs).totalDegree = 2*Fintype.card G.edgeSet ∧
      2*Fintype.card V ≤ (binaryIncidenceProduct signs).totalDegree := by
  refine ⟨degree_binaryIncidenceProduct signs, ?_⟩
  rw [degree_binaryIncidenceProduct signs]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdeg v)
  rw [G.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card] at h
  simpa [mul_comm] using h

private theorem exp2_le_visits {T : ℕ} (hT : 0 < T) {u : ℝ}
    (h : u * Real.log 2 ≤ Real.log T) : (2:ℝ)^u ≤ T := by
  have hT' : 0 < (T:ℝ) := by exact_mod_cast hT
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (by norm_num) _) hT').mp
  rw [Real.log_rpow (by norm_num)]
  linarith only [h]

/-- The runtime estimates hold for every graph with Appendix A's properties,
so the same graph family serves every fixed schedule exponent. -/
theorem theorems3_and6_of_expanding_graphs {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) :
    ∃ C₃ C₆ Cᵤ : ℝ, 0 < C₃ ∧ 0 < C₆ ∧ 0 < Cᵤ ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v, 2 ≤ G.degree v ∧ G.degree v ≤ 3) → HasBalancedCuts G →
        (∀ C ∈ ExpansionGraph.positiveGraphCNF G, C.length = 2 ∧ ∀ l ∈ C, l.2 = true) ∧
        (∀ v, ExpansionGraph.occurs v (ExpansionGraph.positiveGraphCNF G) ≤ 3) ∧
        ∀ {Q r R d₀ T : ℕ}
          (L : PhysicalLayout (Fin n) (Fin (ExpansionGraph.positiveGraphCNF G).length) Q r R)
          (_W : Visits L d₀ T), L.scope = formulaScope (ExpansionGraph.positiveGraphCNF G) →
          c₀*(n:ℝ) ≤ d₀ →
          (L.balanced → (2:ℝ)^(C₃*arbitraryNodeScale n) ≤ T) ∧
          (L.balanced → (r:ℝ)^(2*Q) ≤ (n:ℝ)^A → C₆*((n:ℝ)*scheduledRate n) ≤ Real.log T) ∧
          (ScansAtEveryNode L T → (2:ℝ)^(Cᵤ*arbitraryNodeScale n) ≤ T) := by
  have hδ : (0:ℝ) < 1/32768 := by norm_num
  have hΔ : 0 < (3:ℕ) := by decide
  have hρ : (0:ℝ) < 2/5 := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a, ha, N₃, h3⟩ := balanced_from_candidates hδ hΔ hρ hc₀ 10
  obtain ⟨b, hb, N₆, h6⟩ := scheduled_from_candidates hA hδ hΔ hρ hc₀ 10
  obtain ⟨c, hc, Nᵤ, hu⟩ := unbalanced_from_candidates hδ hΔ hc₀
  refine ⟨a/Real.log 2,b,c/Real.log 2,div_pos ha hlog,hb,div_pos hc hlog,
    max 1 (max N₃ (max N₆ Nᵤ)),?_⟩
  intro n hn G _ hd hcuts
  simp only [max_le_iff] at hn
  have hn0 : 0 < n := by omega
  refine ⟨positiveGraph_clause_shape G,fun v => (positiveGraph_occurrences G v).trans_le (hd v).2,?_⟩
  intro Q r R d₀ T L W hscope hd₀
  let B := positiveGraphFactors G L hscope
  have hn' : 0 < Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn0
  have hρ' : (2/5:ℝ)*(Fintype.card (Fin n):ℝ) ≤ Fintype.card (Fin n) := by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Fin n))]
  have hsub : (2/5:ℝ)*(Fintype.card (Fin n):ℝ) ≤ B.originalSet.card := by
    simpa only [B.card_originalSet] using hρ'
  have hd₀' : c₀*(Fintype.card (Fin n):ℝ) ≤ d₀ := by simpa only [Fintype.card_fin] using hd₀
  refine ⟨?_,?_,?_⟩
  · intro hbal
    have hh := h3 W B.originalSet (by simpa only [Fintype.card_fin] using hn.2.1) hsub hd₀' hbal
      (B.balanced_candidates hcuts hn' hd hρ' hbal)
    apply exp2_le_visits W.visits_pos
    have he : (a/Real.log 2 * arbitraryNodeScale n) * Real.log 2 = a*arbitraryNodeScale n := by field_simp
    rw [he]
    simpa only [Fintype.card_fin] using hh
  · intro hbal hs
    simpa only [Fintype.card_fin] using h6 W B.originalSet
      (by simpa only [Fintype.card_fin] using hn.2.2.1) hsub hd₀'
      (by simpa only [Fintype.card_fin] using hs) (B.balanced_candidates hcuts hn' hd hρ' hbal)
  · intro scans
    have hB : B.originalSet = Finset.univ := by
      change (Finset.univ : Finset (Fin n)).map (Function.Embedding.refl _) = Finset.univ
      exact Finset.map_refl
    have hh := hu W (by simpa only [Fintype.card_fin] using hn.2.2.2) hd₀' scans (fun h =>
      ⟨by simpa only [hB] using B.candidates hcuts hn' hd h⟩)
    apply exp2_le_visits W.visits_pos
    have he : (c/Real.log 2 * arbitraryNodeScale n) * Real.log 2 = c*arbitraryNodeScale n := by field_simp
    rw [he]
    simpa only [Fintype.card_fin] using hh

/-- The shared graph family for Theorems 3 and 6, and the unbalanced Section 6
variant, obtained from the proved graph existence theorem of Appendix A. -/
theorem theorems3_and6_graph_family {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) :
    ∃ C₃ C₆ Cᵤ : ℝ, 0 < C₃ ∧ 0 < C₆ ∧ 0 < Cᵤ ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, 128 ∣ n → ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
        (∀ C ∈ ExpansionGraph.positiveGraphCNF G, C.length = 2 ∧ ∀ l ∈ C, l.2 = true) ∧
        (∀ v, ExpansionGraph.occurs v (ExpansionGraph.positiveGraphCNF G) ≤ 3) ∧
        ∀ {Q r R d₀ T : ℕ}
          (L : PhysicalLayout (Fin n) (Fin (ExpansionGraph.positiveGraphCNF G).length) Q r R)
          (_W : Visits L d₀ T), L.scope = formulaScope (ExpansionGraph.positiveGraphCNF G) →
          c₀*(n:ℝ) ≤ d₀ →
          (L.balanced → (2:ℝ)^(C₃*arbitraryNodeScale n) ≤ T) ∧
          (L.balanced → (r:ℝ)^(2*Q) ≤ (n:ℝ)^A → C₆*((n:ℝ)*scheduledRate n) ≤ Real.log T) ∧
          (ScansAtEveryNode L T → (2:ℝ)^(Cᵤ*arbitraryNodeScale n) ≤ T) := by
  obtain ⟨C₃,C₆,Cᵤ,h₃,h₆,hᵤ,n₀,h⟩ := theorems3_and6_of_expanding_graphs hA hc₀
  refine ⟨C₃,C₆,Cᵤ,h₃,h₆,hᵤ,max 1 n₀,?_⟩
  intro n hn hdiv
  obtain ⟨G,hG,hd,hcuts⟩ := ExpansionGraph.exists_expanding_graph
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left ..).trans hn)) hdiv
  letI := hG
  exact ⟨G,hG,h n ((le_max_right ..).trans hn) G hd hcuts⟩

/-- Appendix A.2 with the runtime conclusions on the parsimonious extension.
Padding bits and gate bits are part of the physical variables. Only the padded
original variables are used in the rank estimates. -/
theorem parsimonious_extension_runtime {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) :
    ∃ C₃ C₆ : ℝ, 0 < C₃ ∧ 0 < C₆ ∧ ∃ N₀ : ℕ, ∀ {n w : ℕ}
      (F : CNF (Fin n)) (_hw : ExpansionGraph.WidthAtMost F w),
      ∃ G : SimpleGraph (PaddedVar n), ∃ _ : DecidableRel G.Adj,
        let H := ExpansionGraph.gateExtension G (ExpansionGraph.padCNF F)
        let N := Fintype.card (GateVar G)
        Nat.card (ExpansionGraph.Models H) = Nat.card (ExpansionGraph.Models F) ∧
        2*N ≤ 5*(n+ExpansionGraph.paddingCount n) ∧
        H.length = F.length+ExpansionGraph.paddingCount n+3*Fintype.card G.edgeSet ∧
        ExpansionGraph.WidthAtMost H (max 3 w) ∧
        (∀ v, ExpansionGraph.occurs (.inl v) H ≤ ExpansionGraph.occurs v (ExpansionGraph.padCNF F)+6) ∧
        (∀ e, ExpansionGraph.occurs (.inr e) H = 3) ∧
        ∀ {Q r R d₀ T : ℕ} (L : PhysicalLayout (GateVar G) (Fin H.length) Q r R)
          (_W : Visits L d₀ T), L.scope = formulaScope H → N₀ ≤ N → c₀*(N:ℝ) ≤ d₀ →
          L.balanced → (2:ℝ)^(C₃*arbitraryNodeScale N) ≤ T ∧
            ((r:ℝ)^(2*Q) ≤ (N:ℝ)^A → C₆*((N:ℝ)*scheduledRate N) ≤ Real.log T) := by
  have hδ : (0:ℝ) < 1/32768 := by norm_num
  have hΔ : 0 < (3:ℕ) := by decide
  have hρ : (0:ℝ) < 2/5 := by norm_num
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨a,ha,N₃,h3⟩ := balanced_from_candidates hδ hΔ hρ hc₀ 10
  obtain ⟨b,hb,N₆,h6⟩ := scheduled_from_candidates hA hδ hΔ hρ hc₀ 10
  refine ⟨a/Real.log 2,b,div_pos ha hlog,hb,max 1 (max N₃ N₆),?_⟩
  intro n w F hw
  obtain ⟨G,hG,hd,hcuts,hcount,hsize,hclause,hwidth⟩ :=
    ExpansionGraph.exists_parsimonious_expanding_extension F hw
  letI := hG
  refine ⟨G,hG,hcount,hsize,hclause,hwidth,?_,?_,?_⟩
  · intro v
    rw [ExpansionGraph.gateExtension_occurs_old]
    have hv := (hd v).2
    omega
  · exact ExpansionGraph.gateExtension_occurs_new G (ExpansionGraph.padCNF F)
  · intro Q r R d₀ T L W hscope hN hd₀ hbal
    let B := gateGraphFactors G (ExpansionGraph.padCNF F) L hscope
    have hN1 : 1 ≤ Fintype.card (GateVar G) := (le_max_left ..).trans hN
    have hX : 0 < Fintype.card (PaddedVar n) := by
      have hsizeN : 2*Fintype.card (GateVar G) ≤ 5*Fintype.card (PaddedVar n) := by
        simpa only [PaddedVar, Fintype.card_sum, Fintype.card_fin] using hsize
      omega
    have hN' : max N₃ N₆ ≤ Fintype.card (GateVar G) := (le_max_right ..).trans hN
    have hsize' : (2:ℝ)*(Fintype.card (GateVar G):ℝ) ≤ 5*(Fintype.card (PaddedVar n):ℝ) := by
      exact_mod_cast (show 2*Fintype.card (GateVar G) ≤ 5*Fintype.card (PaddedVar n) by
        simpa only [PaddedVar, Fintype.card_sum, Fintype.card_fin] using hsize)
    have hρ' : (2/5:ℝ)*(Fintype.card (GateVar G):ℝ) ≤ Fintype.card (PaddedVar n) := by linarith only [hsize']
    have hsub : (2/5:ℝ)*(Fintype.card (GateVar G):ℝ) ≤ B.originalSet.card := by
      simpa only [B.card_originalSet] using hρ'
    have hcan := B.balanced_candidates hcuts hX hd hρ' hbal
    refine ⟨?_, fun hs => h6 W B.originalSet ((le_max_right ..).trans hN') hsub hd₀ hs hcan⟩
    apply exp2_le_visits W.visits_pos
    have hh := h3 W B.originalSet ((le_max_left ..).trans hN') hsub hd₀ hbal hcan
    have he : (a/Real.log 2 * arbitraryNodeScale (Fintype.card (GateVar G))) * Real.log 2 =
        a*arbitraryNodeScale (Fintype.card (GateVar G)) := by field_simp
    rwa [he]

end

end Reconstruction.VisitRuntime
