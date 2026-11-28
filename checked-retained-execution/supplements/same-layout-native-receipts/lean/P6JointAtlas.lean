import J9R20SameFileCatalog
import P6JointReserve

namespace Paper6JointSeating
open scoped Classical
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J9R20SameFile

abbrev Wires (Pair H : Type) := Wire Pair (OrdinaryWire Pair H)
abbrev Clones (Pair : Type) := Pin Pair × Index

variable {Pair H : Type} (ends : H×Bool ≃ Pin Pair×Fin 3)

def clonePort : Wires Pair H → Bool
  | .inl (_,b) => b
  | .inr (_,b) => b

noncomputable def associatedClone : Wires Pair H → Clones Pair
  | .inl (p,_) => (p,none)
  | .inr ((.inl g,k),_) => ((ends (g,k)).1, some (ends (g,k)).2)
  | .inr ((.inr (p,i),k),_) => (p,if k then cycle i else i)

def cloneWireOf : Wires Pair H → Wires Pair H
  | .inl (p,_) => .inl (p,true)
  | .inr (r,_) => .inr (r,true)

theorem clone_wire_is_clone (w : Wires Pair H) : clonePort (cloneWireOf w) = true := by
  rcases w with ⟨p,b⟩|⟨r,b⟩ <;> rfl

theorem clone_wire_same_row (w : Wires Pair H) :
    rowNode Prod.fst (cloneWireOf w) = rowNode Prod.fst w := by
  rcases w with ⟨p,b⟩|⟨r,b⟩ <;> rfl

theorem clone_wire_of_injOn :
    Set.InjOn (rowNode (Pair:=Pair) (Row:=OrdinaryRow Pair H) Prod.fst)
      {w : Wires Pair H | clonePort w = true} := by
  rintro (⟨p,b⟩|⟨r,b⟩) hb (⟨q,c⟩|⟨s,c⟩) hc h <;>
    simp only [Set.mem_setOf_eq, clonePort] at hb hc <;> subst b <;> subst c <;>
    simp_all [rowNode]

theorem associatedClone_eq_of_row (x y : Wires Pair H)
    (h : rowNode Prod.fst x = rowNode Prod.fst y) :
    associatedClone ends x = associatedClone ends y := by
  rcases x with ⟨p,b⟩|⟨r,b⟩ <;> rcases y with ⟨q,c⟩|⟨s,c⟩ <;>
    simp only [rowNode, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · subst q; rfl
  · subst s; rcases r with ⟨j,k⟩; cases j <;> rfl

theorem clone_port_owner_exact (w : Wires Pair H) (h : clonePort w = true) :
    colNode (column ends cycle) w = .inr (cloneOwner (associatedClone ends w)) := by
  rcases w with ⟨p,b⟩|⟨⟨g,k⟩,b⟩ <;> simp only [clonePort] at h <;> subst b
  · rfl
  · cases g with
    | inl e => rfl
    | inr v =>
      rcases v with ⟨p,i⟩
      cases h : (if k then cycle i else i) <;>
        simp [colNode,column,route,cloneOwner,associatedClone,h]

theorem clone_port_owner_reverse [Fintype Pair] [Fintype H] (w : Wires Pair H) (x : Clones Pair)
    (h : colNode (column ends cycle) w = .inr (cloneOwner x)) :
    clonePort w = true ∧ associatedClone ends w = x := by
  have htrue : clonePort w = true := by
    rcases w with ⟨p,b⟩|⟨⟨g,k⟩,b⟩ <;> cases b <;> try rfl
    · simp [colNode] at h
    · rcases x with ⟨x,i⟩
      cases i <;> simp [colNode,column,route,cloneOwner] at h
  exact ⟨htrue,cloneOwner_injective (Sum.inr.inj ((clone_port_owner_exact ends w htrue).symm.trans h))⟩

#print axioms clone_wire_is_clone
#print axioms clone_wire_same_row
#print axioms clone_wire_of_injOn
#print axioms associatedClone_eq_of_row
#print axioms clone_port_owner_exact
#print axioms clone_port_owner_reverse
end Paper6JointSeating



