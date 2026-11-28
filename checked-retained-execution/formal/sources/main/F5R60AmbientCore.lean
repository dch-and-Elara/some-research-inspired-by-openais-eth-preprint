import F5R59ConflictRequests
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! The actual two halves in v8 F5. Edges retain one orientation each,
with disjoint constructor tags for the old graph, the cubic backbone,
and the matching. Both endpoints are part of the constructed graph. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical

variable {n : ℕ}

abbrev Vertices (n : ℕ) := Fin n ⊕ Fin n

abbrev ForwardEdge (G : SimpleGraph (Fin n)) :=
  {e : Fin n × Fin n // e.1 < e.2 ∧ G.Adj e.1 e.2}

noncomputable instance forwardFintype (G : SimpleGraph (Fin n)) :
    Fintype (ForwardEdge G) := Fintype.ofFinite _

abbrev Edge (H B : SimpleGraph (Fin n)) := (ForwardEdge H ⊕ ForwardEdge B) ⊕ Fin n

def oldEdge {H B : SimpleGraph (Fin n)} (e : ForwardEdge H) : Edge H B := .inl (.inl e)
def backboneEdge {H B : SimpleGraph (Fin n)} (e : ForwardEdge B) : Edge H B := .inl (.inr e)
def matchEdge {H B : SimpleGraph (Fin n)} (i : Fin n) : Edge H B := .inr i

def ends (H B : SimpleGraph (Fin n)) : Edge H B → Bool → Vertices n
  | .inl (.inl e), false => .inl e.val.1
  | .inl (.inl e), true => .inl e.val.2
  | .inl (.inr e), false => .inr e.val.1
  | .inl (.inr e), true => .inr e.val.2
  | .inr i, false => .inl i
  | .inr i, true => .inr i

def joinedAdj (H B : SimpleGraph (Fin n)) : Vertices n → Vertices n → Prop
  | .inl i, .inl j => H.Adj i j
  | .inr i, .inr j => B.Adj i j
  | .inl i, .inr j => i = j
  | .inr i, .inl j => i = j

def joined (H B : SimpleGraph (Fin n)) : SimpleGraph (Vertices n) where
  Adj := joinedAdj H B
  symm := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact H.symm h
    · exact Eq.symm h
    · exact Eq.symm h
    · exact B.symm h
  loopless := by
    intro x
    rcases x with x | x
    · exact H.loopless x
    · exact B.loopless x

theorem joined_vertices_card : Fintype.card (Vertices n) = 2*n := by
  simp [Vertices]
  omega

theorem tagged_edges_card (H B : SimpleGraph (Fin n)) :
    Fintype.card (Edge H B) = Fintype.card (ForwardEdge H)+Fintype.card (ForwardEdge B)+n := by
  simp only [Edge,Fintype.card_sum,Fintype.card_fin]

def orient (G : SimpleGraph (Fin n)) {i j : Fin n} (h : G.Adj i j) : ForwardEdge G :=
  if hlt : i < j then ⟨(i,j),hlt,h⟩
  else ⟨(j,i),(lt_of_le_of_ne (le_of_not_gt hlt) (G.ne_of_adj h).symm),G.symm h⟩

theorem orient_endpoints (G : SimpleGraph (Fin n)) {i j : Fin n} (h : G.Adj i j) :
    (orient G h).val = (i,j) ∨ (orient G h).val = (j,i) := by
  unfold orient
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem actual_edges_are_joined (H B : SimpleGraph (Fin n)) (e : Edge H B) :
    (joined H B).Adj (ends H B e false) (ends H B e true) := by
  rcases e with ((e | e) | j)
  · exact e.property.2
  · exact e.property.2
  · rfl

theorem joined_adj_iff_tagged_edge (H B : SimpleGraph (Fin n)) (u v : Vertices n) :
    (joined H B).Adj u v ↔ ∃ e : Edge H B,
      ((ends H B e false = u ∧ ends H B e true = v) ∨
       (ends H B e false = v ∧ ends H B e true = u)) := by
  constructor
  · intro h
    rcases u with i | i <;> rcases v with j | j
    · have hG : H.Adj i j := h
      refine ⟨oldEdge (orient H hG), ?_⟩
      change (Sum.inl (orient H hG).val.1 = Sum.inl i ∧ Sum.inl (orient H hG).val.2 = Sum.inl j) ∨
        (Sum.inl (orient H hG).val.1 = Sum.inl j ∧ Sum.inl (orient H hG).val.2 = Sum.inl i)
      rcases orient_endpoints H hG with e | e
      · rw [e]; exact Or.inl ⟨rfl,rfl⟩
      · rw [e]; exact Or.inr ⟨rfl,rfl⟩
    · have e : i = j := h
      subst j
      exact ⟨matchEdge i, Or.inl ⟨rfl,rfl⟩⟩
    · have e : i = j := h
      subst j
      exact ⟨matchEdge i, Or.inr ⟨rfl,rfl⟩⟩
    · have hG : B.Adj i j := h
      refine ⟨backboneEdge (orient B hG), ?_⟩
      change (Sum.inr (orient B hG).val.1 = Sum.inr i ∧ Sum.inr (orient B hG).val.2 = Sum.inr j) ∨
        (Sum.inr (orient B hG).val.1 = Sum.inr j ∧ Sum.inr (orient B hG).val.2 = Sum.inr i)
      rcases orient_endpoints B hG with e | e
      · rw [e]; exact Or.inl ⟨rfl,rfl⟩
      · rw [e]; exact Or.inr ⟨rfl,rfl⟩
  · rintro ⟨e, ⟨l,r⟩ | ⟨l,r⟩⟩
    · exact l ▸ r ▸ actual_edges_are_joined H B e
    · exact l ▸ r ▸ (joined H B).symm (actual_edges_are_joined H B e)

theorem unordered_joined_edge_unique (H B : SimpleGraph (Fin n)) (e e' : Edge H B)
    (h : (ends H B e false = ends H B e' false ∧ ends H B e true = ends H B e' true) ∨
        (ends H B e false = ends H B e' true ∧ ends H B e true = ends H B e' false)) :
    e=e' := by
  rcases h with h | h
  · rcases e with ((a | b) | i) <;> rcases e' with ((a' | b') | i')
    all_goals simp only [ends,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      false_and,and_false] at h
    · have hh : a=a' := Subtype.ext (Prod.ext h.1 h.2)
      subst a'
      rfl
    · have hh : b=b' := Subtype.ext (Prod.ext h.1 h.2)
      subst b'
      rfl
    · exact congrArg (Sum.inr : Fin n → Edge H B) h.1
  · exfalso
    rcases e with ((a | b) | i) <;> rcases e' with ((a' | b') | i')
    all_goals simp only [ends,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
      false_and,and_false] at h
    · have p := a.property.1
      have q := a'.property.1
      rw [h.1,h.2] at p
      exact (not_lt_of_ge p.le) q
    · have p := b.property.1
      have q := b'.property.1
      rw [h.1,h.2] at p
      exact (not_lt_of_ge p.le) q

theorem actual_matching_endpoints (H B : SimpleGraph (Fin n)) (i : Fin n) :
    ends H B (matchEdge i) false = .inl i ∧ ends H B (matchEdge i) true = .inr i :=
  ⟨rfl,rfl⟩

theorem every_vertex_touches_matching (H B : SimpleGraph (Fin n)) (x : Vertices n) :
    ∃ i : Fin n, x = ends H B (matchEdge i) false ∨ x = ends H B (matchEdge i) true := by
  rcases x with i | i
  · exact ⟨i,Or.inl rfl⟩
  · exact ⟨i,Or.inr rfl⟩

variable {C V : Type}

def conflictGraph (S : F5R59.ClauseSystem C V) : SimpleGraph (F5R59.Vertex S) where
  Adj := F5R59.conflict S
  symm := fun _ _ => F5R59.graph_symmetric S
  loopless := F5R59.graph_irreflexive S

def paddedH (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n) :
    SimpleGraph (Fin n) := (conflictGraph S).map key

theorem enabled_old_conflict_iff (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (x y : F5R59.Vertex S) : (paddedH S key).Adj (key x) (key y) ↔ F5R59.conflict S x y := by
  change ((conflictGraph S).map key).Adj (key x) (key y) ↔ _
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    change F5R59.conflict S a b at h
    simpa only [key.injective ha,key.injective hb] using h
  · intro h
    exact ⟨x,y,h,rfl,rfl⟩

theorem padding_isolated_in_old (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (i j : Fin n) (h : ¬ ∃ x, key x = i) : ¬(paddedH S key).Adj i j := by
  intro ha
  obtain ⟨x,_y,_he,hx,_hy⟩ := (SimpleGraph.map_adj key (conflictGraph S) i j).1 ha
  exact h ⟨x,hx⟩

#print axioms joined_vertices_card
#print axioms tagged_edges_card
#print axioms orient_endpoints
#print axioms actual_edges_are_joined
#print axioms joined_adj_iff_tagged_edge
#print axioms unordered_joined_edge_unique
#print axioms actual_matching_endpoints
#print axioms every_vertex_touches_matching
#print axioms enabled_old_conflict_iff
#print axioms padding_isolated_in_old
end F5R60.Ambient
