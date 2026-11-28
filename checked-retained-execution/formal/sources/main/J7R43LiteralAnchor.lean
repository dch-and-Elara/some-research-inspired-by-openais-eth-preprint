import J6R14SpecializedBoxModeChart

/-! At the original odd centre the singleton address carries the actual
source page and physical parity, plus the requested order. No rechart
or anonymous same-cardinality moment is involved. -/
namespace J7R43Literal
open scoped Classical BigOperators
open P11FullPacking J6R9PacketScopes J8Physical J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {G R S V : Type} [LinearOrder G] {U : V→Type} {a b p : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ w, rowGroup mask i (d.seat w) = d.rowLabel w.1)
variable (hc : ∀ w, colGroup mask i (d.seat w) = actualColLabel d w)

theorem singleton_address_same_tile (hi : i.val=0) (s : S)
    (off : d.rowLabel (pinWire d s).1≠d.pinLabel s) (n : Fin (p-1)) :
    let m := anchoredMode d mask i hr hc s off n
    m.page=(d.seat (pinWire d s)).1 ∧
    m.tile.val=(d.seat (pinWire d s)).2.val%2 ∧
    m.order.val=n.val ∧
    source mask i m=d.pinLabel s ∧
    target mask i m=((d.seat (pinWire d s)).1,d.rowLabel (pinWire d s).1) := by
  refine ⟨rfl,?_,rfl,anchored_source d mask i hr hc s off n,anchored_target d mask i hr hc s off n⟩
  change J6R9PacketTiles.tile i.val (d.seat (pinWire d s)).2.val = _
  rw [hi]
  rfl

#print axioms singleton_address_same_tile
end
end J7R43Literal