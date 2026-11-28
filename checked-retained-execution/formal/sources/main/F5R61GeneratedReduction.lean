import F5R61PreprocessDecision
import F5R61GeneratedCycles

/-! Both occurrence passes are generated. The old conflict positions are
embedded into a same-order ambient backbone. Physical cycle constraints are
the actual output of the original paired-list algorithm. -/
namespace F5R61
set_option autoImplicit false
open F5R59 F5R60
open F5R61.Preprocess F5R60.Ambient

variable {V : Type} [DecidableEq V] {m n : Nat}
variable (S : ClauseSystem (Fin m) V) (w : ∀ c, S.width c = 3)

local notation "P" => (copied S (initialOrder S w))

theorem generated_both_passes_decide
    (k : Vertex P ↪ Fin n) (B : SimpleGraph (Fin n))
    (v : Listing (Vertices n)) (e : Listing (Edge (paddedH P k) B))
    (t : Listing (TripleClause P)) :
    let G := requestGraph P k B
    let D := generatedPrintedCycles G v e t
    (∃ b d, PhysicalPrinted G D b d) ↔ ∃ a : V → Bool, satisfies S a :=
  source_width_three_actual_F1_decision S w k B
    (generatedPrintedCycles (requestGraph P k B) v e t)

#print axioms generated_both_passes_decide
end F5R61
