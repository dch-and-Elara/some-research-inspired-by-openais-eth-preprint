import VisitSigned

/-!
The standalone arbitrary-node signed graph family for Theorem 3. The shared
signed definitions, evaluation, degree and runtime results come from VisitSigned.
-/

namespace Reconstruction.VisitRuntime

/-- The constant and threshold depend only on the charge constant, uniformly
over the signs and the number of nodes. -/
theorem theorem3_signed_graph_family {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, 128 ∣ n →
      ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
        ∀ signs : G.edgeSet → Bool × Bool,
          (∀ c ∈ signedGraphCNF G signs, c.length = 2) ∧
          (∀ v, ExpansionGraph.occurs v (signedGraphCNF G signs) ≤ 3) ∧
          ∀ {Q r R d₀ T : ℕ}
            (L : PhysicalLayout (Fin n) (Fin (signedGraphCNF G signs).length) Q r R)
            (_W : Visits L d₀ T), L.scope = formulaScope (signedGraphCNF G signs) →
            c₀*(n:ℝ) ≤ d₀ → L.balanced → (2:ℝ)^(C*arbitraryNodeScale n) ≤ T := by
  obtain ⟨C₃, _, _, h₃, _, _, n₀, h⟩ :=
    theorems3_and6_signed_graphs (A := 1) zero_lt_one hc₀
  refine ⟨C₃, h₃, max 1 n₀, ?_⟩
  intro n hn hdiv
  obtain ⟨G, hG, hdeg, hcuts⟩ := ExpansionGraph.exists_expanding_graph
    (lt_of_lt_of_le Nat.zero_lt_one ((le_max_left ..).trans hn)) hdiv
  letI := hG
  refine ⟨G, hG, fun signs => ⟨?_, ?_, ?_⟩⟩
  · intro clause hc
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hc
    rfl
  · intro v
    rw [signedGraphCNF_occurs]
    exact (hdeg v).2
  · intro Q r R d₀ T L W hscope hd₀
    exact (h n ((le_max_right ..).trans hn) G hdeg hcuts signs L W hscope hd₀).1

end Reconstruction.VisitRuntime
