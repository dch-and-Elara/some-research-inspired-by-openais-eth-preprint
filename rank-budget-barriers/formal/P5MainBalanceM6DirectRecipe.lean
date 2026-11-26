import P5MainBalanceM6DirectChart
import P5MainBalanceM6Grade
import Mathlib.Tactic.FinCases

/-! Literal rational factor menu for all three kinds of clauses in the
four-clone CNF: signed unary, positive edge, and implication. All term
ports are physically typed, and signs affect only the pin coefficients. -/
namespace P5MainBalance.M6.Direct
open P5MainBalance P5MainBalance.M6 P5MainIterator Polynomial
open scoped BigOperators Classical

variable {V Copy I B : Type*} [LinearOrder B]
variable {graph : Finset (V×V)} {left right : graph→Fin 4}

def pin (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) (v : V) :
    {e : MainClonedCNF.Port graph // L.physical.factor e=(.inl v:Factor graph)} :=
  ⟨.inl v,by rw [L.factor_is]; rfl⟩

def edge (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) (u : graph) (b : Bool) :
    {e : MainClonedCNF.Port graph // L.physical.factor e=(.inr (.inl u):Factor graph)} :=
  ⟨.inr (.inl (u,b)),by rw [L.factor_is]; rfl⟩

def cycle (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) (v : V) (i : Fin 4) (b : Bool) :
    {e : MainClonedCNF.Port graph // L.physical.factor e=(.inr (.inr (v,i)):Factor graph)} :=
  ⟨.inr (.inr (v,i,b)),by rw [L.factor_is]; rfl⟩

private def terms (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) :
    (f : Factor graph)→Fin 4→List {e : MainClonedCNF.Port graph // L.physical.factor e=f}
  | .inl v => ![[],[pin L v],[],[]]
  | .inr (.inl u) => ![[],[edge L u false],[edge L u true],[edge L u false,edge L u true]]
  | .inr (.inr (v,i)) => ![[],[cycle L v i false],[cycle L v i true],[cycle L v i false,cycle L v i true]]

def pinSign (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) (v : V)
    (s : {u : V // signedOwner L.physical (MainClonedCNF.pinPort graph) u=(.inl v:Factor graph)}→Bool) :
    Bool := s ⟨v,marked_pin_owner L v⟩

private def weights (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) :
    (f : Factor graph)→({v : V // signedOwner L.physical (MainClonedCNF.pinPort graph) v=f}→Bool)→Fin 4→ℚ
  | .inl v, s => ![if pinSign L v s then 0 else 1,if pinSign L v s then 1 else -1,0,0]
  | .inr (.inl _), _ => ![0,1,1,-1]
  | .inr (.inr _), _ => ![1,-1,0,1]

noncomputable def recipe (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) :
    SourceRecipe L.physical (MainClonedCNF.pinPort graph) where
  count _ := 4
  degree f i := (terms L f i).length
  read f i j := (terms L f i).get j
  coeff f i s := C (weights L f s i)

noncomputable def actualClauseFactor (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (A : MainClonedCNF.Port graph→Bivariate) :
    (f : Factor graph)→({v : V // signedOwner L.physical (MainClonedCNF.pinPort graph) v=f}→Bool)→Bivariate
  | .inl v, s => if pinSign L v s then A (pin L v).val else 1-A (pin L v).val
  | .inr (.inl u), _ => A (edge L u false).val+A (edge L u true).val -
      A (edge L u false).val*A (edge L u true).val
  | .inr (.inr (v,i)), _ => 1-A (cycle L v i false).val+
      A (cycle L v i false).val*A (cycle L v i true).val

set_option maxHeartbeats 7500000 in
theorem factorScore_literal (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right)
    (A : MainClonedCNF.Port graph→Bivariate) (f : Factor graph)
    (s : {v : V // signedOwner L.physical (MainClonedCNF.pinPort graph) v=f}→Bool) :
    (recipe L).factorScore f s A=actualClauseFactor L A f s := by
  rcases f with v|u|⟨v,i⟩
  · cases h : pinSign L v s <;>
      simp [Recipe.factorScore,recipe,terms,weights,actualClauseFactor,h,
        Fin.sum_univ_succ]
    ring
  · simp [Recipe.factorScore,recipe,terms,weights,actualClauseFactor,
      Fin.sum_univ_succ,Fin.prod_univ_succ]
    ring
  · simp [Recipe.factorScore,recipe,terms,weights,actualClauseFactor,
      Fin.sum_univ_succ,Fin.prod_univ_succ]
    ring

set_option maxHeartbeats 4600000 in
theorem graded_literal (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) :
    (recipe L).graded width 0 := by
  intro f k _ j _
  change (terms L f k).length≤width f+0*j
  rcases f with v|e|q <;> fin_cases k <;> simp [terms,width]

#print axioms factorScore_literal
#print axioms graded_literal
end P5MainBalance.M6.Direct
