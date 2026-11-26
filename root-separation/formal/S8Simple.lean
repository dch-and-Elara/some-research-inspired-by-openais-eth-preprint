import S8Triangle

namespace S8.Triangle

open GraphCutMoments

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem internal_orientation (u v : Vertex U) (h : (u,v) ∈ (internal : Finset _)) :
    u.1 = v.1 ∧ ((u.2 = 0 ∧ v.2 = 1) ∨ (u.2 = 1 ∧ v.2 = 2) ∨ (u.2 = 2 ∧ v.2 = 0)) := by
  rw [internal_mem, triangleEdges_mem] at h
  rcases h with h | h | h
  · rcases Prod.mk.inj h with ⟨hu,hv⟩
    exact ⟨(congrArg Prod.fst hv).symm, Or.inl ⟨congrArg Prod.snd hu, congrArg Prod.snd hv⟩⟩
  · rcases Prod.mk.inj h with ⟨hu,hv⟩
    exact ⟨(congrArg Prod.fst hv).symm, Or.inr (Or.inl ⟨congrArg Prod.snd hu, congrArg Prod.snd hv⟩)⟩
  · rcases Prod.mk.inj h with ⟨hu,hv⟩
    exact ⟨(congrArg Prod.fst hv).symm, Or.inr (Or.inr ⟨congrArg Prod.snd hu, congrArg Prod.snd hv⟩)⟩

theorem exterior_crosses_base (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (loopless : ∀ u, (u,u) ∉ H) (u v : Vertex U) (h : (u,v) ∈ exterior H reg) :
    u.1 ≠ v.1 := by
  rcases Finset.mem_map.mp h with ⟨⟨⟨x,y⟩,he⟩,_,xy⟩
  simp only [exteriorEmbedding, Function.Embedding.coeFn_mk, Prod.mk.injEq] at xy
  obtain ⟨rfl,rfl⟩ := xy
  change x ≠ y
  rintro rfl
  exact loopless x he

/-- The lifted finite edge set stores each undirected edge in only one
    direction. Together with graph_loopless and graph_cubic this gives the
    simple cubic graph stipulated in §8. -/
theorem graph_no_reverse (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (loopless : ∀ u, (u,u) ∉ H) (u v : Vertex U) (h : (u,v) ∈ graph H reg) :
    (v,u) ∉ graph H reg := by
  intro hr
  simp only [graph, Finset.mem_union] at h hr
  rcases h with h | h <;> rcases hr with hr | hr
  · have ha := (internal_orientation u v h).2
    have hb := (internal_orientation v u hr).2
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> omega
  · exact exterior_crosses_base H reg loopless v u hr (internal_orientation u v h).1.symm
  · exact exterior_crosses_base H reg loopless u v h (internal_orientation v u hr).1.symm
  · rcases Finset.mem_map.mp h with ⟨e,_,he⟩
    rcases Finset.mem_map.mp hr with ⟨f,_,hf⟩
    have hh : endpoint H reg e false = endpoint H reg f true :=
      (congrArg Prod.fst he).trans (congrArg Prod.snd hf).symm
    have hb := congrArg Prod.snd
      (endpoint_injective H reg hh : ((e,false) : H × Bool) = (f,true))
    contradiction

#print axioms graph_no_reverse

end S8.Triangle

