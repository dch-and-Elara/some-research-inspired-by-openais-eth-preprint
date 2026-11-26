import MainClonedCNF
import P5MainBalanceM6Origin

/-! Fixed clause and incidence tags of the actual four-clone CNF,
independent of its variable pin signs. -/
namespace P5MainBalance.M6.Direct
open P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Factor (graph : Finset (V×V)) := V ⊕ (graph ⊕ (V×Fin 4))

omit [Fintype V] [DecidableEq V] in
def factorOf (graph : Finset (V×V)) : MainClonedCNF.Port graph→Factor graph
  | .inl v => .inl v
  | .inr (.inl q) => .inr (.inl q.1)
  | .inr (.inr q) => .inr (.inr (q.1,q.2.1))

omit [Fintype V] [DecidableEq V] in
def ownerOf (graph : Finset (V×V)) (left right : graph→Fin 4) :
    MainClonedCNF.Port graph→V×Fin 4
  | .inl v => (v,0)
  | .inr (.inl (e,false)) => (e.val.1,left e)
  | .inr (.inl (e,true)) => (e.val.2,right e)
  | .inr (.inr (v,i,false)) => (v,i)
  | .inr (.inr (v,i,true)) => (v,i+1)

variable {Copy I B : Type*} [LinearOrder B]

/-- This is the literal factor list used by the source layout, not a
semantic assumption about its output or an arbitrary circuit proxy. -/
structure Chart (graph : Finset (V×V)) (left right : graph→Fin 4) where
  physical : SourceLayout (MainClonedCNF.Port graph) (V×Fin 4) (Factor graph) Copy I B
  factor_is : physical.factor=factorOf graph
  owner_is : physical.placement.owner=ownerOf graph left right

omit [Fintype V] [DecidableEq V] in
theorem marked_pin_owner {graph : Finset (V×V)} {left right : graph→Fin 4}
    (L : Chart (Copy:=Copy) (I:=I) (B:=B) graph left right) (v : V) :
    signedOwner L.physical (MainClonedCNF.pinPort graph) v=(.inl v:Factor graph) := by
  simp only [signedOwner,Function.comp_apply,L.factor_is]
  rfl

omit [Fintype V] [DecidableEq V] in
def width {graph : Finset (V×V)} : Factor graph→ℕ
  | .inl _ => 1
  | .inr _ => 2

omit [DecidableEq V] in
theorem sum_width_eq_port_card (graph : Finset (V×V)) :
    (∑ f : Factor graph,width f)=Fintype.card (MainClonedCNF.Port graph) := by
  simp only [Factor,MainClonedCNF.Port,Fintype.sum_sum_type,width,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Finset.sum_const,nsmul_eq_mul,
    Finset.card_univ]
  norm_cast
  omega

#print axioms marked_pin_owner
#print axioms sum_width_eq_port_card
end P5MainBalance.M6.Direct
