import F5R60AmbientDecision
import F5R60PhysicalF1

/-! Source reduction at the actual physical F1 occurrence variables.
The starting formula here is the width-two/three occurrence-copied
instance. The named cycle order is a certified input; this statement
does not implement the initial occurrence-copy pass or choose that order. -/
namespace F5R60
set_option autoImplicit false

theorem actual_ambient_F1_decision
    {C V : Type} {n : Nat}
    (S : F5R59.ClauseSystem C V) (key : F5R59.Vertex S ↪ Fin n)
    (B : SimpleGraph (Fin n))
    (widths : ∀ c, S.width c = 2 ∨ S.width c = 3)
    (D : PrintedCycles (Ambient.requestGraph S key B)) :
    (∃ b d, PhysicalPrinted (Ambient.requestGraph S key B) D b d) ↔
      ∃ a : V → Bool, F5R59.satisfies S a :=
  (actual_F1_sat_iff_allowed (Ambient.requestGraph S key B) D).trans
    (Ambient.actual_ambient_requests_iff S key B widths)

#print axioms actual_ambient_F1_decision
end F5R60

