import V8PooledRangeCopies
import Mathlib.Data.Finset.SDiff

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

/-! Closed line-graph two-neighbourhoods of the same labeled cubic graph.
No independence, randomized thinning, or chosen matching is assumed. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange
noncomputable section

variable {V E : Type*} [Fintype E] (G : Graph V E)

def share (e f : E) : Prop := ∃ b c : Bool, G e b=G f c

omit [Fintype E] in
theorem share_symm {e f : E} (h : share G e f) : share G f e := by
  obtain ⟨b,c,h⟩ := h
  exact ⟨c,b,h.symm⟩

def withinTwo (e f : E) : Prop :=
  share G e f ∨ ∃ z, share G e z ∧ share G z f

omit [Fintype E] in
theorem withinTwo_symm {e f : E} (h : withinTwo G e f) : withinTwo G f e := by
  rcases h with h | ⟨z,h₁,h₂⟩
  · exact Or.inl (share_symm G h)
  · exact Or.inr ⟨z,share_symm G h₂,share_symm G h₁⟩

def neighbors (e : E) : Finset E := Finset.univ.filter (fun f => f≠e ∧ share G e f)

theorem mem_neighbors (e f : E) : f∈neighbors G e ↔ f≠e ∧ share G e f := by
  simp only [neighbors,Finset.mem_filter,Finset.mem_univ,true_and]

def selfPort (e : E) (b : Bool) : Incidence G (G e b) := ⟨(e,b),rfl⟩

def otherPorts (e : E) (b : Bool) : Finset (Incidence G (G e b)) :=
  (Finset.univ : Finset (Incidence G (G e b))).erase (selfPort G e b)

def otherEdges (e : E) (b : Bool) : Finset E :=
  (otherPorts G e b).image (fun a => a.val.1)

theorem other_ports_card (p : ThreePorts G) (e : E) (b : Bool) :
    (otherPorts G e b).card=2 := by
  rw [otherPorts,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,
    Fintype.card_congr (p (G e b)),Fintype.card_fin]

theorem other_edges_cap (p : ThreePorts G) (e : E) (b : Bool) :
    (otherEdges G e b).card≤2 := by
  unfold otherEdges
  exact Finset.card_image_le.trans (other_ports_card G p e b).le

theorem neighbors_cap (p : ThreePorts G) (e : E) : (neighbors G e).card≤4 := by
  have hs : neighbors G e⊆otherEdges G e false ∪ otherEdges G e true := by
    intro f hf
    obtain ⟨hne,b,c,h⟩ := (mem_neighbors G e f).mp hf
    have hm : f∈otherEdges G e b := by
      apply Finset.mem_image.mpr
      refine ⟨⟨(f,c),h.symm⟩,?_,rfl⟩
      apply Finset.mem_erase.mpr
      refine ⟨fun hh => hne (congrArg (fun a : Incidence G (G e b) => a.val.1) hh),
        Finset.mem_univ _⟩
    cases b
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ hm
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add (other_edges_cap G p e false)
      (other_edges_cap G p e true)))

theorem reverse_neighbor {e f : E} (h : f∈neighbors G e) : e∈neighbors G f := by
  obtain ⟨hne,he⟩ := (mem_neighbors G e f).mp h
  exact (mem_neighbors G f e).mpr ⟨Ne.symm hne,share_symm G he⟩

def ball (e : E) : Finset E :=
  insert e (neighbors G e ∪ (neighbors G e).biUnion (fun f => (neighbors G f).erase e))

theorem ball_contains (e : E) : e∈ball G e := Finset.mem_insert_self _ _

theorem ball_contains_share {e f : E} (h : share G e f) : f∈ball G e := by
  by_cases he : f=e
  · subst f
    exact ball_contains G e
  · apply Finset.mem_insert_of_mem
    exact Finset.mem_union_left _ ((mem_neighbors G e f).mpr ⟨he,h⟩)

theorem ball_contains_two {e f : E} (h : withinTwo G e f) : f∈ball G e := by
  rcases h with h | ⟨z,hz,hf⟩
  · exact ball_contains_share G h
  · by_cases he : f=e
    · subst f
      exact ball_contains G e
    · by_cases hze : z=e
      · subst z
        exact ball_contains_share G hf
      · by_cases hfz : f=z
        · subst f
          exact ball_contains_share G hz
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨z,(mem_neighbors G e z).mpr ⟨hze,hz⟩,
            Finset.mem_erase.mpr ⟨he,(mem_neighbors G z f).mpr ⟨hfz,hf⟩⟩⟩

theorem ball_cap (p : ThreePorts G) (e : E) : (ball G e).card≤17 := by
  have hErased (f : E) (hf : f∈neighbors G e) : ((neighbors G f).erase e).card≤3 := by
    rw [Finset.card_erase_of_mem (reverse_neighbor G hf)]
    have hc := neighbors_cap G p f
    omega
  have h₂ : ((neighbors G e).biUnion (fun f => (neighbors G f).erase e)).card≤12 := by
    calc
      _ ≤ ∑ f ∈ neighbors G e, ((neighbors G f).erase e).card := Finset.card_biUnion_le
      _ ≤ ∑ _f ∈ neighbors G e, 3 := Finset.sum_le_sum hErased
      _ = (neighbors G e).card*3 := by simp
      _ ≤ _ := Nat.mul_le_mul_right 3 (neighbors_cap G p e)
  unfold ball
  apply (Finset.card_insert_le e _).trans
  have hc := Finset.card_union_le (neighbors G e)
    ((neighbors G e).biUnion (fun f => (neighbors G f).erase e))
  have h₁ := neighbors_cap G p e
  omega

#print axioms share_symm
#print axioms withinTwo_symm
#print axioms other_ports_card
#print axioms neighbors_cap
#print axioms reverse_neighbor
#print axioms ball_contains_two
#print axioms ball_cap
end
end V8NativeMessage.C2Physical
