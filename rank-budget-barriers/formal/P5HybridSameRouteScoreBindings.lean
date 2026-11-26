import P5HybridSameRouteConditioning
import P5HybridMainOnlyPrimitives
import P5HybridDOnlyKey

/-! Interpret the four-word conditionals on the exact key projections used
by both actual dual-coordinate collision arguments. -/
namespace Paper5.HybridSameRouteConditioning
open scoped Classical BigOperators
open GuardExpectation J1MainSourceLabels

set_option autoImplicit false
set_option warningAsError true

section MAIN
variable {V F B I S E : Type*} [Fintype V] [Fintype F] [Fintype B] [Fintype I]
  [Fintype S] [DecidableEq I] [DecidableEq V] [DecidableEq F] [DecidableEq B]

def mainKeys (ties : I → F → Option B) (vars : E → V) (fac : E → F) :
    E → Bool → I → Primitive V F B I :=
  fun e side i => if side then HybridMainOnly.factorKeyAt ties (fac e) i else .inl (vars e,i)

theorem main_agreement_exact (ties : I → F → Option B) (vars : E → V) (fac : E → F) (e f : E)
    (w : Primitive V F B I → S → ℚ) (hw : ∀ p, ∑ a, w p a=1) :
    average w (fun z=>J1MainSourceCollision.indicator
      (HybridMainOnly.twoCell ties vars fac z e=HybridMainOnly.twoCell ties vars fac z f)) =
    average (fun i : support (mainKeys ties vars fac) e f=>w i)
      (fun z=>J1MainSourceCollision.indicator
        (restrictCell (mainKeys ties vars fac) e f z false=restrictCell (mainKeys ties vars fac) e f z true)) :=
  agreement_exact (mainKeys ties vars fac) e f w hw

end MAIN

section D
variable {U V T I S E : Type*} [Fintype U] [Fintype V] [Fintype T] [Fintype I]
  [Fintype S] [DecidableEq U] [DecidableEq V] [DecidableEq T] [DecidableEq I]

def dKeys (tags : I→U→Option T) (row : E→U) (col : E→V) : E→Bool→I→HybridDOnly.Atom U V T I :=
  fun e side i=>if side then HybridDOnly.freeAtom (col e) i else HybridDOnly.tiedAtom tags (row e) i

theorem d_agreement_exact (tags : I→U→Option T) (row : E→U) (col : E→V) (e f : E)
    (w : HybridDOnly.Atom U V T I→S→ℚ) (hw : ∀ p,∑ a,w p a=1) :
    average w (fun z=>J1MainSourceCollision.indicator
      (HybridDOnly.orderedCell tags row col z e=HybridDOnly.orderedCell tags row col z f)) =
    average (fun i : support (dKeys tags row col) e f=>w i)
      (fun z=>J1MainSourceCollision.indicator
        (restrictCell (dKeys tags row col) e f z false=restrictCell (dKeys tags row col) e f z true)) :=
  agreement_exact (dKeys tags row col) e f w hw
end D

end Paper5.HybridSameRouteConditioning
#print axioms Paper5.HybridSameRouteConditioning.main_agreement_exact
#print axioms Paper5.HybridSameRouteConditioning.d_agreement_exact
