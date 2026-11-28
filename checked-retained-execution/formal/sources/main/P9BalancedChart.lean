import P11FullPackingLaw
import GuardAssembly

/-! The deterministic P9 layout uses the same actual address chart as
P11, with every orientation used b times rather than one shared mask. -/

namespace P9BalancedChart
open P11FullPacking GuardedPacking

variable {K : Type*} [LinearOrder K] {a b : ℕ}

def balancedMask (a b : ℕ) (K : Type*) [LinearOrder K] : MaskFamily a b K :=
  fun _ p => p.2

def OrientedEnd (k : Key (Fin a) K) (c : Orient k) (right : Bool) :=
  {z : TypeCellFiber (balancedMask a b K) k c // z.2.val = endpointIndex a right}

def orientedEndEquiv (k : Key (Fin a) K) (c : Orient k) (right : Bool) :
    OrientedEnd (b:=b) k c right ≃ Fin b where
  toFun z := z.val.1.1
  invFun j := ⟨⟨(j,endMask right c),⟨endpointIndex a right, by
    rw [show (balancedMask a b K) k (j,endMask right c) = endMask right c by rfl,
      slotOrient_endpoint k _ right _ rfl, endMask_involutive right c]⟩⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨⟨p,m⟩,⟨x,hx⟩⟩,he⟩
    change x = endpointIndex a right at he
    subst x
    change slotOrient k m (endpointIndex a right) = c at hx
    rw [slotOrient_endpoint k m right (endpointIndex a right) rfl] at hx
    have hm := congrArg (endMask right) hx
    rw [endMask_involutive right m] at hm
    subst m
    rfl
  right_inv j := rfl

theorem oriented_end_card (k : Key (Fin a) K) (c : Orient k) (right : Bool) :
    Nat.card (OrientedEnd (b:=b) k c right) = b :=
  (Nat.card_congr (orientedEndEquiv (b:=b) k c right)).trans (Nat.card_fin b)

abbrev ActualEnd (a b : ℕ) {K : Type*} [LinearOrder K]
    (γ : Cell (Fin a) K) (right : Bool) :=
  {z : Physical a b K // physicalCell (balancedMask a b K) z = γ ∧ z.2 = endpointIndex a right}

/-- The actual full physical position, with its true sorted type and
orientation, not an injected abstract seat. -/
def physicalEndEquiv (γ : Cell (Fin a) K) (right : Bool) :
    ActualEnd a b γ right ≃ Fin b where
  toFun z := z.val.1.2.1
  invFun j := ⟨(⟨key γ,(j,endMask right (orientation γ))⟩,endpointIndex a right),by
    constructor
    · change cell (key γ)
        (slotOrient (key γ) (endMask right (orientation γ)) (endpointIndex a right)) = γ
      rw [slotOrient_endpoint (key γ) _ right _ rfl, endMask_involutive right, cell_decode]
    · rfl⟩
  left_inv := by
    rintro ⟨⟨⟨k,⟨j,m⟩⟩,x⟩,hcell,hx⟩
    change x = endpointIndex a right at hx
    subst x
    change cell k (slotOrient k m (endpointIndex a right)) = γ at hcell
    rw [slotOrient_endpoint k m right _ rfl] at hcell
    have hk : k = key γ := (key_cell k (endMask right m)).symm.trans (congrArg key hcell)
    subst k
    have hm : endMask right m = orientation γ :=
      cell_injective (key γ) (hcell.trans (cell_decode γ).symm)
    have hm' := congrArg (endMask right) hm
    rw [endMask_involutive right m] at hm'
    subst m
    rfl
  right_inv j := rfl

theorem actual_end_card (γ : Cell (Fin a) K) (right : Bool) :
    Nat.card (ActualEnd a b γ right) = b :=
  (Nat.card_congr (physicalEndEquiv (b:=b) γ right)).trans (Nat.card_fin b)

theorem different_ends (ha : 0 < a) :
    endpointIndex a false ≠ endpointIndex a true := by
  intro e
  have hL : 2 ≤ 2^a := by
    exact (pow_one 2).symm.trans_le (Nat.pow_le_pow_right (by decide) ha)
  have he := congrArg Fin.val e
  exact endpoints_ne hL he

#print axioms oriented_end_card
#print axioms physicalEndEquiv
#print axioms actual_end_card
#print axioms different_ends

end P9BalancedChart