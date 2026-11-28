import J1R43LiteralMarginal
import J1MainSourceCollision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false

/-! Each term of the printed J1 objective is a literal incidence pair,
ordinary variable pair, single diagonal pin hit, or simultaneous diagonal
pin hit. The reused factorKey includes the designated triangle tie.
Finite local support retains the sharing even after partial assignment. -/
namespace J1R43Literal
open scoped BigOperators
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance

section LiteralEvents
variable {V F B I S E : Type*} [DecidableEq V] [DecidableEq F] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Nonempty S]

local notation "P" => Primitive V F B I

abbrev Roles := Bool × Bool

def pairKeys (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (e e' : E) (u : Roles × I) : P :=
  let z := if u.1.1 then e' else e
  if u.1.2 then .inr (factorKey special tie (fac z) u.2)
    else .inl (var z,u.2)

def pairRead (z : Roles × I → S) (e : Bool) : Draw I S :=
  (fun i => z ((e,false),i),fun i => z ((e,true),i))

theorem pairRead_is_source (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (e e' : E) (z : P → S) (j : Bool) :
    pairRead (z ∘ pairKeys special tie var fac e e') j =
      literalCell special tie var fac z (if j then e' else e) := by
  cases j <;> rfl

def incidenceEvent (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (e e' : E) : LocalTest P S :=
  LocalTest.fromReads (pairKeys special tie var fac e e')
    (fun z => decide (pairRead z false = pairRead z true))

theorem incidenceEvent_value (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (e e' : E) (z : P → S) :
    (incidenceEvent special tie var fac e e').value z =
      indicator (literalCell special tie var fac z e = literalCell special tie var fac z e') := by
  rw [incidenceEvent,read_value]
  simp only [pairRead_is_source]
  unfold indicator
  simp

def variableEvent (v w : V) (t : I) : LocalTest P S :=
  LocalTest.fromReads (fun b : Bool × I => Sum.inl ((if b.1 then w else v),b.2))
    (fun z => decide (z (false,t) = z (true,t)))

theorem variableEvent_value (v w : V) (t : I) (z : P → S) :
    (variableEvent v w t).value z =
      indicator (variableWord z v t = variableWord z w t) := by
  rw [variableEvent,read_value]
  simp [indicator, variableWord]

def hitPairEvent (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (t : I) (g : S) (e e' : E) : LocalTest P S :=
  LocalTest.fromReads (pairKeys special tie var fac e e')
    (fun z => decide (((pairRead z false).1 = (pairRead z false).2 ∧
      (pairRead z false).1 t = g) ∧
      ((pairRead z true).1 = (pairRead z true).2 ∧ (pairRead z true).1 t = g)))

theorem hitPairEvent_value (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (t : I) (g : S) (e e' : E) (z : P → S) :
    (hitPairEvent special tie var fac t g e e').value z =
      hit t g (literalCell special tie var fac z e) * hit t g (literalCell special tie var fac z e') := by
  rw [hitPairEvent,read_value]
  simp only [pairRead_is_source]
  let x := literalCell special tie var fac z e
  let y := literalCell special tie var fac z e'
  change (if decide ((x.1=x.2 ∧ x.1 t=g) ∧ (y.1=y.2 ∧ y.1 t=g)) then 1 else 0) =
    hit t g x * hit t g y
  classical
  by_cases hx : x.1=x.2 ∧ x.1 t=g <;> by_cases hy : y.1=y.2 ∧ y.1 t=g <;>
    simp [hit, hx, hy]

theorem singleHitEvent_value (special : I) (tie : F → Option B) (var : E → V) (fac : E → F)
    (t : I) (g : S) (e : E) (z : P → S) :
    (hitPairEvent special tie var fac t g e e).value z =
      hit t g (literalCell special tie var fac z e) := by
  rw [hitPairEvent_value,← pow_two,hit_sq]

theorem incidenceEvent_completions
    (special : I) (tie : F → Option B) (var : E → V) (fac : E → F) (e f : E) :
    Fintype.card ((incidenceEvent (S:=S) special tie var fac e f).support → S) ≤
      (Fintype.card S ^ Fintype.card I)^4 := by
  apply local_completions
  simp [Roles]

theorem variableEvent_completions (v w : V) (t : I) :
    Fintype.card ((variableEvent (F:=F) (B:=B) (S:=S) v w t).support → S) ≤
      (Fintype.card S ^ Fintype.card I)^4 := by
  apply local_completions
  simp

theorem hitPairEvent_completions
    (special : I) (tie : F → Option B) (var : E → V) (fac : E → F) (t : I) (g : S) (e f : E) :
    Fintype.card ((hitPairEvent special tie var fac t g e f).support → S) ≤
      (Fintype.card S ^ Fintype.card I)^4 := by
  apply local_completions
  simp [Roles]

end LiteralEvents

#print axioms pairRead_is_source
#print axioms incidenceEvent_value
#print axioms variableEvent_value
#print axioms hitPairEvent_value
#print axioms singleHitEvent_value
#print axioms incidenceEvent_completions
#print axioms variableEvent_completions
#print axioms hitPairEvent_completions

end J1R43Literal