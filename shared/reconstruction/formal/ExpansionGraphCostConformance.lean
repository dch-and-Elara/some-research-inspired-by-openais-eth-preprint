import ExpansionGraphCost

namespace Reconstruction.ExpansionGraph

noncomputable section

private def unorderedEdge {n : ℕ} (uv : PaddedVar n × PaddedVar n) :
    Sym2 (PaddedVar n) :=
  s(uv.1, uv.2)

/-- A supplied list presents the graph when it contains each undirected
edge exactly once. These fields certify the input and are never consulted
by the construction. -/
structure PresentsGraph {n : ℕ} (L : EdgeInput n) (G : SimpleGraph (PaddedVar n)) : Prop where
  edges : ∀ e, e ∈ L.map unorderedEdge ↔ e ∈ G.edgeSet
  unique : (L.map unorderedEdge).Nodup

private def edgeAt {n : ℕ} {L : EdgeInput n} {G : SimpleGraph (PaddedVar n)}
    (h : PresentsGraph L G) (i : Fin L.length) : G.edgeSet :=
  ⟨unorderedEdge (L.get i), (h.edges _).mp (List.mem_map.mpr ⟨_, List.get_mem L i, rfl⟩)⟩

private theorem edgeAt_bijective {n : ℕ} {L : EdgeInput n} {G : SimpleGraph (PaddedVar n)}
    (h : PresentsGraph L G) : Function.Bijective (edgeAt h) := by
  constructor
  · intro i j hij
    have hget : (L.map unorderedEdge)[i.val]'(by rw [List.length_map]; exact i.isLt) =
        (L.map unorderedEdge)[j.val]'(by rw [List.length_map]; exact j.isLt) := by
      simpa only [List.getElem_map] using congrArg Subtype.val hij
    apply Fin.ext
    exact h.unique.getElem_inj_iff.mp hget
  · intro e
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((h.edges e.val).mpr e.property)
    refine ⟨⟨i.val, by simpa using i.isLt⟩, Subtype.ext ?_⟩
    simpa [edgeAt, List.get_eq_getElem] using hi

/-- Rename fresh variables by their undirected graph edge instead of their
position in the supplied list. The padded variable identifiers are fixed. -/
def suppliedVariableEquiv {n : ℕ} {L : EdgeInput n} {G : SimpleGraph (PaddedVar n)}
    (h : PresentsGraph L G) : OutputVar n L.length ≃ GateVar G :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.ofBijective (edgeAt h) (edgeAt_bijective h))

private theorem edgeAt_and {n : ℕ} {L : EdgeInput n} {G : SimpleGraph (PaddedVar n)}
    (h : PresentsGraph L G) (x : GateVar G → Bool) (j : Fin L.length) :
    (x (.inl (L.get j).1) && x (.inl (L.get j).2)) =
      (x (.inl (endpoints G (edgeAt h j)).1) && x (.inl (endpoints G (edgeAt h j)).2)) := by
  have H : s((L.get j).1, (L.get j).2) =
      s((endpoints G (edgeAt h j)).1, (endpoints G (edgeAt h j)).2) :=
    (endpoints_eq G (edgeAt h j)).symm
  rcases Sym2.eq_iff.mp H with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
  · rw [hu,hv,Bool.and_comm]

private theorem reference_sat {n : ℕ} (F : CNF (Fin n))
    (G : SimpleGraph (PaddedVar n)) [DecidableRel G.Adj] (x : GateVar G → Bool) :
    Satisfies (gateExtension G (padCNF F)) x ↔
      Satisfies F (fun v => x (.inl (.inl v))) ∧
      (∀ v : Fin (paddingCount n), x (.inl (.inr v)) = false) ∧
      ∀ e : G.edgeSet, x (.inr e) = (x (.inl (endpoints G e).1) && x (.inl (endpoints G e).2)) := by
  rw [satisfies_gateExtension, satisfies_padCNF]
  constructor
  · rintro ⟨⟨hF,hPad⟩, hG⟩
    exact ⟨hF,hPad,fun e => congrFun hG (.inr e)⟩
  · rintro ⟨hF,hPad,hG⟩
    refine ⟨⟨hF,hPad⟩, ?_⟩
    funext v
    cases v with
    | inl v => rfl
    | inr e => exact hG e

/-- For every assignment, the list construction agrees with the reference
gate extension after renaming the gate variables. This allows arbitrary
edge order and either order of the endpoints in every supplied record. -/
theorem constructFromEdges_conforms {n : ℕ} (F : CNF (Fin n)) {L : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj]
    (h : PresentsGraph L G) (x : GateVar G → Bool) :
    Satisfies (constructFromEdges F L).output (x ∘ suppliedVariableEquiv h) ↔
      Satisfies (gateExtension G (padCNF F)) x := by
  rw [constructFromEdges_sat, reference_sat]
  have he :
      (∀ j : Fin L.length, x (.inr (edgeAt h j)) =
        (x (.inl (L.get j).1) && x (.inl (L.get j).2))) ↔
      (∀ e : G.edgeSet, x (.inr e) = (x (.inl (endpoints G e).1) && x (.inl (endpoints G e).2))) := by
    constructor
    · intro hall e
      obtain ⟨j, rfl⟩ := (edgeAt_bijective h).2 e
      exact (hall j).trans (edgeAt_and h x j)
    · intro hall j
      exact (hall (edgeAt h j)).trans (edgeAt_and h x j).symm
  exact and_congr_right fun _ => and_congr_right fun _ => he

/-- The correspondence of satisfying assignments with the reference model. -/
def suppliedModelsEquiv {n : ℕ} (F : CNF (Fin n)) {L : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj] (h : PresentsGraph L G) :
    Models (constructFromEdges F L).output ≃ Models (gateExtension G (padCNF F)) where
  toFun x := ⟨x.val ∘ (suppliedVariableEquiv h).symm, by
    apply (constructFromEdges_conforms F h _).mp
    have he : (x.val ∘ (suppliedVariableEquiv h).symm) ∘ suppliedVariableEquiv h = x.val := by
      funext v
      simp
    rw [he]
    exact x.property⟩
  invFun y := ⟨y.val ∘ suppliedVariableEquiv h, (constructFromEdges_conforms F h _).mpr y.property⟩
  left_inv _ := Subtype.ext (by funext v; simp)
  right_inv _ := Subtype.ext (by funext v; simp)

/-- The edge-list construction is parsimonious, including the padding. -/
def constructFromEdges_models {n : ℕ} (F : CNF (Fin n)) {L : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj] (h : PresentsGraph L G) :
    Models F ≃ Models (constructFromEdges F L).output :=
  (parsimonious_extension F G).trans (suppliedModelsEquiv F h).symm

/-- Appendix A.2 with an explicit construction, its cost, and its
assignment equivalence to the original formula. -/
theorem constructFromEdges_linear_parsimonious {n : ℕ} (F : CNF (Fin n)) {L : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj] (h : PresentsGraph L G) :
    (constructFromEdges F L).steps ≤ 895 + 24*(F.length + (F.map List.length).sum + L.length) ∧
      Nat.card (Models (constructFromEdges F L).output) = Nat.card (Models F) :=
  ⟨constructFromEdges_linear F L, Nat.card_congr (constructFromEdges_models F h).symm⟩

/-- In the appendix's degree-three graph family, the edge term is linear
in the number of padded vertices. -/
theorem constructFromEdges_degree_three_bound {n : ℕ} (F : CNF (Fin n)) {L : EdgeInput n}
    {G : SimpleGraph (PaddedVar n)} [DecidableRel G.Adj] (h : PresentsGraph L G)
    (hd : ∀ v, G.degree v ≤ 3) :
    (constructFromEdges F L).steps ≤
      6 + 3*F.length + 7*(F.map List.length).sum + 7*paddingCount n +
        36*(n + paddingCount n) := by
  have hE : L.length = Fintype.card G.edgeSet := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (Equiv.ofBijective (edgeAt h) (edgeAt_bijective h))
  have hV : Fintype.card (PaddedVar n) = n + paddingCount n := by
    simp only [PaddedVar, Fintype.card_sum, Fintype.card_fin]
  have hSize := (gateExtension_size G hd).1
  rw [Fintype.card_sum, hV, ← hE] at hSize
  rw [constructFromEdges_steps]
  omega

end

end Reconstruction.ExpansionGraph
