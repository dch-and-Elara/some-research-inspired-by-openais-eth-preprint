import MainClonedCNF
import Mathlib.Tactic.FinCases

namespace S8.Triangle

open scoped BigOperators
open GraphCutMoments

variable {A U : Type*} [Fintype U] [DecidableEq U]

abbrev Vertex (U : Type*) := U × Fin 3

def triangleEdges (u : U) : Finset (Vertex U × Vertex U) :=
  {((u,0),(u,1)), ((u,1),(u,2)), ((u,2),(u,0))}

def internal : Finset (Vertex U × Vertex U) :=
  Finset.univ.biUnion triangleEdges

noncomputable def endpoint (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (e : H) (b : Bool) : Vertex U :=
  if b then (e.1.2, MainClonedCNF.edgeNumber H reg e.1.2
    (Sum.inr ⟨e.1, Finset.mem_filter.mpr ⟨e.2, rfl⟩⟩))
  else (e.1.1, MainClonedCNF.edgeNumber H reg e.1.1
    (Sum.inl ⟨e.1, Finset.mem_filter.mpr ⟨e.2, rfl⟩⟩))

omit [Fintype U] in
theorem triangleEdges_mem (e : Vertex U × Vertex U) (u : U) :
    e ∈ triangleEdges u ↔ e = ((u,0),(u,1)) ∨ e = ((u,1),(u,2)) ∨ e = ((u,2),(u,0)) := by
  simp [triangleEdges]

theorem internal_mem (e : Vertex U × Vertex U) :
    e ∈ (internal : Finset (Vertex U × Vertex U)) ↔ e ∈ triangleEdges e.1.1 := by
  simp only [internal, Finset.mem_biUnion, Finset.mem_univ, true_and, triangleEdges_mem]
  constructor
  · rintro ⟨u, rfl | rfl | rfl⟩ <;> simp
  · exact fun h => ⟨_, h⟩

/-- Exterior endpoints have a bijective port numbering. -/
theorem endpoint_injective (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    Function.Injective (fun p : H × Bool => endpoint H reg p.1 p.2) := by
  rintro ⟨⟨⟨u,v⟩,he⟩,b⟩ ⟨⟨⟨x,y⟩,hf⟩,c⟩ h
  cases b <;> cases c
  all_goals
    simp only [endpoint, Bool.false_eq_true, if_false, if_true, Prod.mk.injEq] at h
    rcases h with ⟨hvertex, hport⟩
    subst_vars
    have hslot := (MainClonedCNF.edgeNumber H reg _).injective hport
    simp at hslot ⊢ <;> exact hslot

noncomputable def exteriorEmbedding (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    H ↪ Vertex U × Vertex U :=
  ⟨fun e => (endpoint H reg e false, endpoint H reg e true), fun e f eq =>
    have he : ((e,false) : H × Bool) = (f,false) :=
      endpoint_injective H reg (congrArg Prod.fst eq)
    congrArg Prod.fst he⟩

noncomputable def exterior (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    Finset (Vertex U × Vertex U) :=
  Finset.univ.map (exteriorEmbedding H reg)

theorem exterior_disjoint (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (loopless : ∀ u, (u,u) ∉ H) : Disjoint internal (exterior H reg) := by
  rw [Finset.disjoint_left]
  intro e hi he
  rw [exterior, Finset.mem_map] at he
  obtain ⟨f, _, rfl⟩ := he
  have hEq : f.1.1 = f.1.2 := by
    rw [internal_mem,triangleEdges_mem] at hi
    have h : ∀ e : Vertex U × Vertex U, e ∈ triangleEdges (e.1.1) → e.1.1 = e.2.1 := by
      intro e hh
      rcases (triangleEdges_mem e e.1.1).1 hh with h | h | h <;>
        exact congrArg (fun a : Vertex U × Vertex U => a.2.1) h |>.symm
    simpa [exteriorEmbedding, endpoint] using h _ ((triangleEdges_mem _ _).2 hi)
  obtain ⟨⟨u,v⟩,hf⟩ := f
  change u = v at hEq
  subst v
  exact loopless u hf

theorem endpoint_surjective (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    Function.Surjective (fun p : H × Bool => endpoint H reg p.1 p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
    ⟨endpoint_injective H reg, ?_⟩ |>.2
  simpa [Nat.mul_comm] using (regular_edge_count H 3 reg)

theorem exterior_perfect (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (v : Vertex U) : degree (exterior H reg) v = 1 := by
  have card_side (b : Bool) :
      ((exterior H reg).filter fun p => (if b then p.2 else p.1) = v).card =
        (Finset.univ.filter fun e : H => endpoint H reg e b = v).card := by
    cases b <;> simp [exterior, Finset.filter_map, exteriorEmbedding, Function.comp_def]
  obtain ⟨⟨e,b⟩,he⟩ := endpoint_surjective H reg v
  have unique_side (c : Bool) :
      (Finset.univ.filter fun f : H => endpoint H reg f c = v) =
        if c = b then {e} else ∅ := by
    ext f
    have equiv : endpoint H reg f c = v ↔ f = e ∧ c = b := by
      rw [← he]
      exact ⟨fun hf => Prod.mk.inj (endpoint_injective H reg hf),
        fun ⟨rfl,rfl⟩ => rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, equiv]
    by_cases hb : c = b <;> simp [hb]
  unfold degree
  have hleft := card_side false
  have hright := card_side true
  simp only [Bool.false_eq_true, if_false] at hleft
  simp only [if_true] at hright
  rw [hleft, hright, unique_side false, unique_side true]
  cases b <;> simp

theorem internal_degree (v : Vertex U) : degree (internal : Finset _) v = 2 := by
  have left : ((internal : Finset (Vertex U × Vertex U)).filter fun e => e.1 = v) =
      (triangleEdges v.1).filter fun e => e.1 = v := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, rfl⟩
      exact ⟨(internal_mem e).1 he, rfl⟩
    · rintro ⟨he, rfl⟩
      exact ⟨(internal_mem e).2 he, rfl⟩
  have right : ((internal : Finset (Vertex U × Vertex U)).filter fun e => e.2 = v) =
      (triangleEdges v.1).filter fun e => e.2 = v := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨he, rfl⟩
      have hsame : e.1.1 = e.2.1 := by
        rcases (triangleEdges_mem _ _).1 ((internal_mem e).1 he) with h | h | h <;>
          exact (congrArg (fun a : Vertex U × Vertex U => a.2.1) h).symm
      exact ⟨hsame ▸ (internal_mem e).1 he, rfl⟩
    · rintro ⟨he, rfl⟩
      have hsame : e.1.1 = e.2.1 := by
        rcases (triangleEdges_mem _ _).1 he with h | h | h <;>
          exact congrArg (fun a : Vertex U × Vertex U => a.1.1) h
      exact ⟨(internal_mem e).2 (hsame.symm ▸ he), rfl⟩
  unfold degree
  rw [left,right]
  obtain ⟨u,i⟩ := v
  fin_cases i <;> simp [triangleEdges, Finset.filter_insert, Finset.filter_singleton]

noncomputable def graph (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    Finset (Vertex U × Vertex U) := internal ∪ exterior H reg

theorem graph_cubic (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (loopless : ∀ u, (u,u) ∉ H) (v : Vertex U) : degree (graph H reg) v = 3 := by
  have hd := exterior_disjoint H reg loopless
  have h : degree (graph H reg) v = degree internal v + degree (exterior H reg) v := by
    unfold graph degree
    rw [Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    omega
  rw [h, internal_degree, exterior_perfect]

theorem graph_loopless (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (loopless : ∀ u, (u,u) ∉ H) (v : Vertex U) : (v,v) ∉ graph H reg := by
  simp only [graph, Finset.mem_union, not_or]
  refine ⟨?_, ?_⟩
  · rw [internal_mem, triangleEdges_mem]
    rintro (h | h | h) <;> have he := congrArg (fun e : Vertex U × Vertex U => (e.1.2,e.2.2)) h <;>
      simp only [Prod.mk.injEq] at he <;> omega
  · rw [exterior, Finset.mem_map]
    rintro ⟨e, _, he⟩
    have h : endpoint H reg e false = endpoint H reg e true :=
      (congrArg Prod.fst he).trans (congrArg Prod.snd he).symm
    have hb := congrArg Prod.snd
      (endpoint_injective H reg h : ((e,false) : H × Bool) = (e,true))
    contradiction

noncomputable def exteriorOwner (H : Finset (U × U)) (reg : ∀ u, degree H u = 3) :
    Vertex U ≃ H × Bool :=
  (Equiv.ofBijective _ ⟨endpoint_injective H reg, endpoint_surjective H reg⟩).symm

@[simp] theorem exterior_owner (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (e : H) (b : Bool) :
    exteriorOwner H reg (endpoint H reg e b) = (e,b) :=
  (exteriorOwner H reg).apply_symm_apply (e,b)

theorem internal_tie (f : U → A) : ∀ e ∈ (internal : Finset (Vertex U × Vertex U)),
    f e.1.1 = f e.2.1 := by
  intro e he
  rcases (triangleEdges_mem _ _).1 ((internal_mem e).1 he) with h | h | h <;>
    exact congrArg f ((congrArg (fun a : Vertex U × Vertex U => a.2.1) h).symm)

theorem exterior_tie (H : Finset (U × U)) (reg : ∀ u, degree H u = 3)
    (f : H → A) : ∀ e ∈ exterior H reg,
    f (exteriorOwner H reg e.1).1 = f (exteriorOwner H reg e.2).1 := by
  intro e he
  obtain ⟨f', _, rfl⟩ := Finset.mem_map.mp he
  change f (exteriorOwner H reg (endpoint H reg f' false)).1 =
    f (exteriorOwner H reg (endpoint H reg f' true)).1
  simp

#print axioms graph_loopless
#print axioms internal_tie
#print axioms exterior_tie
#print axioms endpoint_injective
#print axioms endpoint_surjective
#print axioms exterior_disjoint
#print axioms exterior_perfect
#print axioms internal_degree
#print axioms graph_cubic

end S8.Triangle

