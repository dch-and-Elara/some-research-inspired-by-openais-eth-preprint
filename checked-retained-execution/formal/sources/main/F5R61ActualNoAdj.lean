import F5R61CycleNoAdj
import F5R61CycleMinSize
import F5R61ForbiddenClassificationAmbient

namespace F5R61
open F5R60 F5R60.Ambient
set_option autoImplicit false

theorem generated_original_repeats_are_not_neighbours
    {V E T : Type} [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]
    (G : RequestGraph V E T) (endsDistinct : DistinctSourceEnds G)
    (incident : ∀ x, ∃ a, G.left a = x ∨ G.right a = x)
    (v : Listing V) (e : Listing E) (t : Listing T)
    (n : Logical V T) (p q : PrivatePos V E T)
    (repeatPair : RepeatInOriginalClause G p q) (i j : Nat)
    (a : (actualCycleList G v e t n)[i]? = some p)
    (b : (actualCycleList G v e t n)[j]? = some q) :
    separated (actualCycleList G v e t n).length i j := by
  obtain ⟨hi,ep⟩ := List.getElem?_eq_some_iff.mp a
  have np : nameOf G p = n :=
    (actualCycleList_exact_members G v e t p n).1 (List.mem_iff_getElem.2 ⟨i,hi,ep⟩)
  have enough := each_actual_cycle_has_four G v e t incident n
  have once := actual_cycle_nodup G v e t n
  rcases (repeat_iff_actual_forbidden_in_fibre G endsDistinct v e t p q n).1 ⟨repeatPair,np⟩ with left|right
  · exact actual_pair_never_neighbours _ _ _ _ left enough once i j a b
  · have z := actual_pair_never_neighbours _ _ _ _ right enough once j i b a
    exact ⟨z.2,z.1⟩

theorem all_ambient_vertices_incident {C V : Type} {n : Nat}
    (S : F5R59.ClauseSystem C V) (k : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (x : Vertices n) :
    ∃ a, (requestGraph S k B).left a = x ∨ (requestGraph S k B).right a = x := by
  obtain ⟨i,left|right⟩ := every_vertex_touches_matching (paddedH S k) B x
  · exact ⟨matchEdge i,Or.inl left.symm⟩
  · exact ⟨matchEdge i,Or.inr right.symm⟩

theorem all_actual_F1_copies_separated_at_source
    {C V : Type} {n : Nat} [DecidableEq C] [Fintype C]
    (S : F5R59.ClauseSystem C V) (k : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (v : Listing (Vertices n)) (e : Listing (Edge (paddedH S k) B)) (t : Listing (TripleClause S))
    (name : Logical (Vertices n) (TripleClause S))
    (p q : PrivatePos (Vertices n) (Edge (paddedH S k) B) (TripleClause S))
    (bad : RepeatInOriginalClause (requestGraph S k B) p q) (i j : Nat)
    (hp : (actualCycleList (requestGraph S k B) v e t name)[i]? = some p)
    (hq : (actualCycleList (requestGraph S k B) v e t name)[j]? = some q) :
    separated (actualCycleList (requestGraph S k B) v e t name).length i j := by
  letI : Fintype (TripleClause S) := Fintype.ofFinite _
  exact generated_original_repeats_are_not_neighbours (requestGraph S k B)
    (actual_ambient_ends_distinct S k B) (all_ambient_vertices_incident S k B)
    v e t name p q bad i j hp hq

#print axioms generated_original_repeats_are_not_neighbours
#print axioms all_ambient_vertices_incident
#print axioms all_actual_F1_copies_separated_at_source
end F5R61
