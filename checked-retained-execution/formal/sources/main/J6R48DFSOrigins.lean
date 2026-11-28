import J6R48DFSScope
import J6R34ChildPathOrigins

/-! The provenance test for stack reclamation is about the literal
graph and actual selected child slots. Original vertices use root
entries; each generated predecessor has a real earlier on-path
birth and a particular physical page. An off-path sibling cannot
be demanded by this typed route. Raw route encoding remains a
separate theorem and is not inferred from a vertex count. -/
namespace J6R48DFS
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34ChildPath J6R21Ancestor

set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 2200

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page

theorem actual_vertex_origin_survives_reclamation (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (initial : L) (rootLive : L→Prop) (stable : StableBank rootLive)
    (root : rootLive initial) (legal : ReadyOnStack born initial)
    (p : Path sel r c) (v : c.host.Row⊕c.host.Col) :
    (∃ u : r.host.Row⊕r.host.Col, Nonempty (Trace (point r.host u) (point c.host v))) ∨
    (∃ (anc : Call (PhysicalHost f ell)) (older : Path sel r anc)
        (w : (Plan sel).Slot anc) (k : PageAt T (older.ticket w)),
      OnPath born (born older w).job p ∧
      IsLive (born older w).job (stackBank born initial p) ∧
      Nonempty (Trace (bornPoint T (older.ticket w) k) (point c.host v))) := by
  rcases actual_path_has_typed_origin born p v with h|h
  · exact Or.inl h
  · obtain ⟨anc,older,w,k,there,trace⟩ := h
    exact Or.inr ⟨anc,older,w,k,there,
      scoped_birth_live born initial rootLive stable root legal p _ there,trace⟩

#print axioms actual_vertex_origin_survives_reclamation
end J6R48DFS
