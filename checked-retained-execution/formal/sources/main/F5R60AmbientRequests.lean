import F5R60AmbientCore
import F5R60LogicalRequests

/-! The original F5 switches and requests on the actual ambient graph.
Every original occurrence has its old-side key; padding and backbone
are disabled. Binary requests are indexed by real old clique edges. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical

variable {C V : Type} {n : ℕ}

abbrev TwoClause (S : F5R59.ClauseSystem C V) := {c : C // S.width c=2}
abbrev TripleClause (S : F5R59.ClauseSystem C V) := {c : C // S.width c=3}

def originalVertex (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (x : F5R59.Vertex S) : Vertices n := .inl (key x)

theorem original_vertex_injective (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) : Function.Injective (originalVertex S key) :=
  fun _ _ eq => key.injective (Sum.inl.inj eq)

noncomputable def available (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n) :
    Vertices n → Bool
  | .inl i => decide (∃ x : F5R59.Vertex S, key x = i)
  | .inr _ => false

theorem available_on_old (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (i : Fin n) : available S key (.inl i) = true ↔ ∃ x : F5R59.Vertex S, key x=i := by
  simp [available]

theorem original_vertex_enabled (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (x : F5R59.Vertex S) : available S key (originalVertex S key x)=true :=
  (available_on_old S key (key x)).2 ⟨x,rfl⟩

theorem padding_vertex_disabled (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (i : Fin n) (h : ¬∃ x : F5R59.Vertex S, key x=i) :
    available S key (.inl i)=false := by
  simp [available,h]

theorem backbone_vertex_disabled (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (i : Fin n) : available S key (.inr i)=false := rfl

def originalConflictEdge (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) {x y : F5R59.Vertex S} (h : F5R59.conflict S x y) :
    Edge (paddedH S key) B :=
  oldEdge (orient (paddedH S key) ((enabled_old_conflict_iff S key x y).2 h))

theorem original_conflict_endpoints (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) {x y : F5R59.Vertex S} (h : F5R59.conflict S x y) :
    let e := originalConflictEdge S key B h
    let E := ends (paddedH S key) B e
    ((E false=originalVertex S key x ∧ E true=originalVertex S key y) ∨
      (E false=originalVertex S key y ∧ E true=originalVertex S key x)) := by
  let H := paddedH S key
  let he : H.Adj (key x) (key y) := (enabled_old_conflict_iff S key x y).2 h
  change (Sum.inl (orient H he).val.1=Sum.inl (key x) ∧
      Sum.inl (orient H he).val.2=Sum.inl (key y)) ∨
    (Sum.inl (orient H he).val.1=Sum.inl (key y) ∧
      Sum.inl (orient H he).val.2=Sum.inl (key x))
  rcases orient_endpoints H he with hx | hy
  · rw [hx]; exact Or.inl ⟨rfl,rfl⟩
  · rw [hy]; exact Or.inr ⟨rfl,rfl⟩

def binaryEdge (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) (c : TwoClause S) : Edge (paddedH S key) B :=
  originalConflictEdge S key B (F5R59.atTwo_edge S c.val c.property)

theorem binary_edge_in_old_half (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) (c : TwoClause S) :
    ∃ e : ForwardEdge (paddedH S key), binaryEdge S key B c = oldEdge e :=
  ⟨_,rfl⟩

noncomputable def edgeActive (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) (e : Edge (paddedH S key) B) : Bool :=
  decide (∃ c : TwoClause S, binaryEdge S key B c=e)

theorem edge_active_iff_original_binary (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (e : Edge (paddedH S key) B) :
    edgeActive S key B e=true ↔ ∃ c : TwoClause S, binaryEdge S key B c=e := by
  simp [edgeActive]

theorem matching_edge_not_requested (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n)) (i : Fin n) :
    edgeActive S key B (matchEdge i)=false := by
  apply Bool.eq_false_iff.mpr
  intro hTrue
  obtain ⟨c,e⟩ := (edge_active_iff_original_binary S key B _).1 hTrue
  obtain ⟨h,r⟩ := binary_edge_in_old_half S key B c
  rw [r] at e
  cases e

theorem backbone_edge_not_requested (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n)) (j : ForwardEdge B) :
    edgeActive S key B (backboneEdge j)=false := by
  apply Bool.eq_false_iff.mpr
  intro hTrue
  obtain ⟨c,e⟩ := (edge_active_iff_original_binary S key B _).1 hTrue
  obtain ⟨h,r⟩ := binary_edge_in_old_half S key B c
  rw [r] at e
  cases e

def tripleVertex (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (t : TripleClause S) (i : Fin 3) : Vertices n :=
  originalVertex S key (F5R59.atThree S t.val t.property i)

theorem triple_vertices_distinct (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (t : TripleClause S) : Function.Injective (tripleVertex S key t) := by
  intro i j e
  have same := original_vertex_injective S key e
  exact Fin.ext (congrArg (fun x : F5R59.Vertex S => x.snd.val) same)

theorem actual_triples_disjoint (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    {s t : TripleClause S} (hne : s≠t) (i j : Fin 3) :
    tripleVertex S key s i≠tripleVertex S key t j := by
  intro e
  apply F5R59.triple_requests_disjoint S s.val t.val s.property t.property
    (fun z => hne (Subtype.ext z)) i j
  exact original_vertex_injective S key e

theorem triple_vertices_actual_clique (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (t : TripleClause S) (i j : Fin 3) (hne : i≠j) :
    (joined (paddedH S key) B).Adj (tripleVertex S key t i) (tripleVertex S key t j) :=
  (enabled_old_conflict_iff S key _ _).2 (F5R59.atThree_clique S t.val t.property i j hne)

/-- There is no externally supplied request geometry: this is the actual
oriented old+new edge family, with only original clause requests enabled. -/
noncomputable def requestGraph (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n)) :
    F5R60.RequestGraph (Vertices n) (Edge (paddedH S key) B) (TripleClause S) where
  left e := ends (paddedH S key) B e false
  right e := ends (paddedH S key) B e true
  first t := tripleVertex S key t 0
  second t := tripleVertex S key t 1
  third t := tripleVertex S key t 2
  available := available S key
  edgeActive := edgeActive S key B
  tripleActive := fun _ => true

#print axioms original_vertex_injective
#print axioms available_on_old
#print axioms original_vertex_enabled
#print axioms padding_vertex_disabled
#print axioms backbone_vertex_disabled
#print axioms original_conflict_endpoints
#print axioms binary_edge_in_old_half
#print axioms edge_active_iff_original_binary
#print axioms matching_edge_not_requested
#print axioms backbone_edge_not_requested
#print axioms triple_vertices_distinct
#print axioms actual_triples_disjoint
#print axioms triple_vertices_actual_clique
#print axioms requestGraph
end F5R60.Ambient
