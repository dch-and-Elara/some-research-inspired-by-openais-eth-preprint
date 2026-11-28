import F5R61ForbiddenClassificationList
import F5R60AmbientRequests

/-! Discharge the distinct-ends guard from the same ambient graph and
clause triples that feed the physical F1 reduction. -/
namespace F5R61
open F5R60 F5R60.Ambient
set_option autoImplicit false

variable {C V : Type} {n : ℕ}

theorem actual_ambient_ends_distinct (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n)) :
    DistinctSourceEnds (requestGraph S key B) where
  edge e := (joined (paddedH S key) B).ne_of_adj (actual_edges_are_joined (paddedH S key) B e)
  triple t :=
    let h := triple_vertices_distinct S key t
    ⟨fun e => (by decide : (0:Fin 3)≠1) (h e),
      fun e => (by decide : (0:Fin 3)≠2) (h e),
      fun e => (by decide : (1:Fin 3)≠2) (h e)⟩

theorem actual_ambient_repeat_iff_forbidden (S : F5R59.ClauseSystem C V)
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (v : Listing (Vertices n)) (e : Listing (Edge (paddedH S key) B)) (t : Listing (TripleClause S))
    (p q : PrivatePos (Vertices n) (Edge (paddedH S key) B) (TripleClause S)) :
    RepeatInOriginalClause (requestGraph S key B) p q ↔
      (p,q) ∈ allForbidden v e t ∨ (q,p) ∈ allForbidden v e t :=
  repeat_iff_actual_forbidden (requestGraph S key B) (actual_ambient_ends_distinct S key B) v e t p q

#print axioms actual_ambient_ends_distinct
#print axioms actual_ambient_repeat_iff_forbidden
end F5R61
