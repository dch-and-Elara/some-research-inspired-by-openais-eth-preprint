import J9R17AllPinsAtlas
import J6R16SpecializedBoxBounds

/-! Physical per-tile order legality is already implied by the
explicit signed precision and cubic size guards. -/
namespace J9R17AllPins
open scoped Classical BigOperators
open J8Physical J6R14SpecializedBox
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype S] [DecidableEq Packet]

theorem all_physical_orders_legal (he : Even L) (hL : 0<L) (M p : ℕ)
    (hcube : L^3≤M) (hp : 10*M≤p) :
    ∀ (s:S) (n : Fin (Fintype.card (PinTile d s))), n.val<p-1 := by
  intro s n
  have hN := (n.isLt.trans_le (pins_per_tile d s he)).trans_le (Nat.div_le_self _ _)
  have hLL : L≤L^3 := by
    calc
      L = L*1 := by rw [mul_one]
      _ ≤ L*L^2 := Nat.mul_le_mul_left _ (Nat.one_le_of_lt (Nat.pow_pos hL))
      _ = L^3 := by ring
  exact signed_slot_order_legal n.val L M p hN (hLL.trans hcube) hp

#print axioms all_physical_orders_legal
end
end J9R17AllPins