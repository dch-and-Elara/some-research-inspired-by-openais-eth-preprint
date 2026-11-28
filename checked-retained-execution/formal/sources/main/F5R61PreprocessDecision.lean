import F5R61Preprocess
import F5R60ActualDecision
import F5R60AmbientDegree

/-! Attach the actual first pass to the already literal F5 conflict
and F1 decision constructions. The ambient matching/backbone and the
different F1 occurrence-cycle chart are not chosen in this module. -/
namespace F5R61.Preprocess
set_option autoImplicit false
set_option warningAsError true
open F5R59 F5R60
variable {V : Type} [DecidableEq V] {m n : ℕ}
variable (S : ClauseSystem (Fin m) V) (width : ∀ c, S.width c = 3)
local notation "P" => (copied S (initialOrder S width))

theorem source_width_three_actual_F1_decision
    (key : Vertex P ↪ Fin n)
    (B : SimpleGraph (Fin n))
    (D : PrintedCycles (Ambient.requestGraph P key B)) :
    (∃ b d, PhysicalPrinted (Ambient.requestGraph P key B) D b d) ↔
      ∃ a : V → Bool, satisfies S a :=
  (actual_ambient_F1_decision P key B
    (copied_width2_or3 S (initialOrder S width) (fun c => Or.inr (width c))) D).trans
      (copied_satisfiable_iff S (initialOrder S width))

theorem preprocessed_ambient_degree_at_most_five
    (key : Vertex P ↪ Fin n) (B : SimpleGraph (Fin n))
    (cubic : ∀ i, Nat.card (Ambient.Neighbor B i)=3) (v : Ambient.Vertices n) :
    Nat.card (Ambient.Neighbor (Ambient.joined (Ambient.paddedH P key) B) v)≤5 :=
  Ambient.actual_ambient_degree_at_most_five P key B
    (fun c => by
      have r := copied_width2_or3 S (initialOrder S width) (fun c => Or.inr (width c)) c
      omega)
    (each_copied_variable_at_most_three S (initialOrder S width)) cubic v

#print axioms source_width_three_actual_F1_decision
#print axioms preprocessed_ambient_degree_at_most_five
end F5R61.Preprocess
