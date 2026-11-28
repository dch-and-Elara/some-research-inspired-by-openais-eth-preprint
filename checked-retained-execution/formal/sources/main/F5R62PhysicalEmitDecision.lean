import F5R62PhysicalEmit
import F5R61PreprocessDecision

/-! Both source occurrence passes now have actual Boolean clause output.
This statement keeps the actual ambient comparison key, cubic model (if
needed by the reduction), and listed graph indices explicit; it does
not claim to generate an external backbone or choose its order. -/
namespace F5R62.PhysicalEmit
set_option autoImplicit false
set_option warningAsError true
open F5R59 F5R60 F5R61 F5R61.Preprocess F5R60.Ambient

variable {V : Type} [DecidableEq V] {m n : ℕ}
variable (S : ClauseSystem (Fin m) V) (w : ∀ c, S.width c = 3)
local notation "P" => (copied S (initialOrder S w))

theorem final_emitted_cnf_decides_original_sat
    (k : Vertex P ↪ Fin n) (B : SimpleGraph (Fin n))
    (v : Listing (Vertices n)) (e : Listing (Edge (paddedH P k) B))
    (t : Listing (TripleClause P)) :
    let G := requestGraph P k B
    (∃ a, CnfSat a (f1ActualCNF G v e t)) ↔ ∃ a : V → Bool, satisfies S a :=
  (emitted_iff_physical (requestGraph P k B) v e t).trans
    (source_width_three_actual_F1_decision S w k B
      (generatedPrintedCycles (requestGraph P k B) v e t))

#print axioms final_emitted_cnf_decides_original_sat
end F5R62.PhysicalEmit
