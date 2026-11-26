import SolverChildren

noncomputable section
namespace RootSeparation.Solver
open scoped BigOperators
open Classical

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable (N : Network R) {P : Type} [Fintype P] {a L : ℕ}
variable (left : N.Row → Fin a → Fin 64) (right : N.Col → Fin a → Fin 64)
variable (i : Fin a)

def splitPorts (Y X : N.Wire → Bool) (g : Fin 64) (w : ChildEdge N left right i g) : Bool :=
  if w.val.2 then X w.val.1 else Y w.val.1

/-- The two bit strings are independent after cutting the wires.
    Each port belongs to exactly one group. -/
def splitPortsEquiv : ((N.Wire → Bool) × (N.Wire → Bool)) ≃
    ((g : Fin 64) → ChildEdge N left right i g → Bool) where
  toFun pair := splitPorts N left right i pair.1 pair.2
  invFun bits :=
    (fun w => bits (left (N.row w) i) ⟨(w,false),rfl⟩,
      fun w => bits (right (N.col w) i) ⟨(w,true),rfl⟩)
  left_inv p := rfl
  right_inv b := by
    funext g w
    rcases w with ⟨⟨w,side⟩,h⟩
    cases side
    · have h' : left (N.row w) i = g := h
      subst g
      rfl
    · have h' : right (N.col w) i = g := h
      subst g
      rfl

theorem oldTable_splitPorts (Y X : N.Wire → Bool) (g : Fin 64) (φ : R →+* S)
    (v : RetainedOld N left right i g) :
    oldTable N left right i g φ v (fun w => splitPorts N left right i Y X g w.val) =
      φ (Sum.elim (fun u => N.rowEntry u (fun w => Y w.val))
        (fun u => N.colEntry u (fun w => X w.val)) v.val) := by
  rcases v with ⟨v|v,hv⟩ <;> rfl

theorem childOldProducts (Y X : N.Wire → Bool) (φ : R →+* S) (put : N.Wire ↪ P × Fin L)
    (tables : (g : Fin 64) → (k : P) →
        ({w // packetEndpoint N left right i g put w = k} → Bool) → S) :
    (∏ g, (childNetwork N left right i g φ put (tables g)).rowProduct
      (splitPorts N left right i Y X g)) = φ (N.rowProduct Y * N.colProduct X) := by
  unfold Network.rowProduct Network.colProduct
  let f (v : N.Row ⊕ N.Col) :=
    φ (Sum.elim (fun u => N.rowEntry u (fun w => Y w.val))
      (fun u => N.colEntry u (fun w => X w.val)) v)
  have h (g : Fin 64) :
      (∏ x : (childNetwork N left right i g φ put (tables g)).Row,
        (childNetwork N left right i g φ put (tables g)).rowEntry x
          (fun w => splitPorts N left right i Y X g w.val)) =
      ∏ x : RetainedOld N left right i g, f x.val := by
    apply Finset.prod_congr rfl
    intro x _
    exact oldTable_splitPorts N left right i Y X g φ x
  simp_rw [h]
  calc
    _ = ∏ v : N.Row ⊕ N.Col, f v := by
      rw [← Fintype.prod_fiberwise (S8.DChild.symbol left right i) f]
    _ = _ := by
      rw [Fintype.prod_sum_type,map_mul,map_prod,map_prod]
      rfl

#print axioms splitPortsEquiv
#print axioms oldTable_splitPorts
#print axioms childOldProducts

end RootSeparation.Solver
