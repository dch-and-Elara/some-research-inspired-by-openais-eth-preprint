import Init

/-! Literal-by-literal zero/one semantics of the printed v8 F1 clauses.
These statements must be applied only after the occurrence cycles agree. -/
namespace F5R60
set_option autoImplicit false

def literalBit (s x : Bool) : Bool := if s then x else !x

def switchClause (s x : Bool) : Bool := (!x) || literalBit s x

def conflictClause (x u : Bool) : Bool := (!x) || (!u)

def edgeClause (t x u : Bool) : Bool := x || u || literalBit t x

def tripleGate (x u y : Bool) : Bool :=
  ((!x) || y) && ((!u) || y) && (x || u || (!y))

def tripleClause (r y z : Bool) : Bool := y || z || literalBit r z

theorem actual_switch (s x : Bool) :
    switchClause s x = true ↔ (x = true → s = true) := by
  cases s <;> cases x <;> decide

theorem actual_conflict (x u : Bool) :
    conflictClause x u = true ↔ ¬ (x = true ∧ u = true) := by
  cases x <;> cases u <;> decide

theorem actual_edge_request (t x u : Bool) :
    edgeClause t x u = true ↔ (t = true → x = true ∨ u = true) := by
  cases t <;> cases x <;> cases u <;> decide

theorem exact_y_gate (x u y : Bool) :
    tripleGate x u y = true ↔ y = (x || u) := by
  cases x <;> cases u <;> cases y <;> decide

theorem actual_triple_request (r x u y z : Bool) :
    tripleGate x u y = true ∧ tripleClause r y z = true ↔
      y = (x || u) ∧ (r = true → x = true ∨ u = true ∨ z = true) := by
  cases r <;> cases x <;> cases u <;> cases y <;> cases z <;> decide

def detachedValues : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

theorem exact_detached_models :
    (detachedValues.filter (fun z => z.1 || z.2)).length = 3 := rfl

#print axioms actual_switch
#print axioms actual_conflict
#print axioms actual_edge_request
#print axioms exact_y_gate
#print axioms actual_triple_request
#print axioms exact_detached_models

end F5R60
