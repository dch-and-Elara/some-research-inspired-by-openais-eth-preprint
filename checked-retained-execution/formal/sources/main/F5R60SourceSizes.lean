import F5R60PhysicalF1
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! The original F1 positions before/after an implication pass are genuine
finite types, not an assumed number of private variables. -/
namespace F5R60
set_option autoImplicit false
variable {V E T : Type}

abbrev PositionShape (V E T : Type) :=
  ((V × Fin 2) ⊕ (E × Fin 2)) ⊕ ((E × Fin 3) ⊕ (T × Fin 10))

def privateEquiv : PrivatePos V E T ≃ PositionShape V E T where
  toFun
    | .sw v i => .inl (.inl (v,i))
    | .cf e i => .inl (.inr (e,i))
    | .er e i => .inr (.inl (e,i))
    | .tr t i => .inr (.inr (t,i))
  invFun
    | .inl (.inl (v,i)) => .sw v i
    | .inl (.inr (e,i)) => .cf e i
    | .inr (.inl (e,i)) => .er e i
    | .inr (.inr (t,i)) => .tr t i
  left_inv p := by cases p <;> rfl
  right_inv p := by
    rcases p with (a|b)|(a|b) <;> cases ‹_ × _› <;> rfl

variable [Fintype V] [Fintype E] [Fintype T]

def privatePositionsFintype : Fintype (PrivatePos V E T) :=
  Fintype.ofEquiv (PositionShape V E T) privateEquiv.symm

local instance : Fintype (PrivatePos V E T) := privatePositionsFintype

def printedK (V E T : Type) [Fintype V] [Fintype E] [Fintype T] : Nat :=
  2*Fintype.card V+5*Fintype.card E+10*Fintype.card T

theorem actual_private_slots (V E T : Type) [Fintype V] [Fintype E] [Fintype T] :
    Fintype.card (PrivatePos V E T) = printedK V E T := by
  rw [Fintype.card_congr (privateEquiv (V:=V) (E:=E) (T:=T))]
  simp only [PositionShape,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,printedK]
  omega

abbrev PhysicalVar (V E T : Type) := PrivatePos V E T ⊕ Bool

theorem actual_declared_F1_variables (V E T : Type) [Fintype V] [Fintype E] [Fintype T] :
    Fintype.card (PhysicalVar V E T) = printedK V E T + 2 := by
  simp only [PhysicalVar,Fintype.card_sum,Fintype.card_bool,actual_private_slots]

abbrev MainWire (V E T : Type) := (PrivatePos V E T ⊕ (PrivatePos V E T × Bool)) ⊕ Bool

theorem actual_F1_wire_index_size (V E T : Type) [Fintype V] [Fintype E] [Fintype T] :
    Fintype.card (MainWire V E T) = 3 * printedK V E T + 2 := by
  simp only [MainWire,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,actual_private_slots]
  omega

#print axioms actual_private_slots
#print axioms actual_declared_F1_variables
#print axioms actual_F1_wire_index_size
end F5R60
