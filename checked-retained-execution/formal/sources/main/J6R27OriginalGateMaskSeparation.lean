
import J6R27OriginalGateAxis

/-! The immutable mode key is deliberately independent of the mask.
A general packing must supply the true page mask, even when its raw
roster, tile, and Taylor-weight words are otherwise identical. -/
namespace J6R27OriginalGate
open P11FullPacking J6R9PacketScopes

theorem opposite_page_masks_exchange_groups {a b : ℕ}
    (i : Fin a) (k : Page a b (Fin 64)) (u : Fin (2^(i.val+1)))
    (hot : (k.1.val i).1≠(k.1.val i).2) :
    let p := (k,tileIndex i u)
    let zero : MaskFamily a b (Fin 64) := fun _ _ _=>false
    let one : MaskFamily a b (Fin 64) := fun _ _ _=>true
    rowGroup zero i p=colGroup one i p ∧
      colGroup zero i p=rowGroup one i p ∧ rowGroup zero i p≠rowGroup one i p := by
  dsimp only
  unfold rowGroup colGroup physicalCell cell
  simp only [dif_pos hot,slotOrient,shiftMask,bits,tileIndex,Fin.coe_castLE]
  cases bit : u.val.testBit i.val <;> simp [hot,Ne.symm hot]

#print axioms opposite_page_masks_exchange_groups
end J6R27OriginalGate


