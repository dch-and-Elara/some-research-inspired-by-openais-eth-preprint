import J9R17AllPinsAtlas

/-! J7 uses the same actual occupied (page,parity) atlas as J9, but
only one individual source child per order and at most one zero-mode
baseline per group. This is a number of calls, not their bit time. -/
namespace J7R43Literal
open scoped Classical
open J8Physical J9R17AllPins
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
variable {Packet R S V : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V (Fin 64) P L)
variable [Fintype S] [Fintype Packet]

abbrev SingleChildOrders := Orders d
abbrev WithBaselines := Fin 64 ⊕ SingleChildOrders d

theorem actual_individual_request_count :
    Fintype.card (SingleChildOrders d) = Fintype.card S :=
  moment_orders_count d

theorem with_all_baselines_request_count :
    Fintype.card (WithBaselines d) = Fintype.card S + 64 := by
  rw [Fintype.card_sum,Fintype.card_fin,actual_individual_request_count,Nat.add_comm]

theorem all_source_calls_at_most_wire_count [Fintype R] :
    Fintype.card (SingleChildOrders d) ≤ Fintype.card (Wire R) := by
  rw [actual_individual_request_count]
  exact pin_card_le_wire_card d

theorem all_bits_from_decoded_individual_tiles
    (obs : ∀ k : Occupied d, Fin (Fintype.card (PinTile d (anchor d k))) → Bool)
    (sign : S→Bool)
    (h : ∀ k i, obs k i=sign (pinEnumeration d (anchor d k) i).val) :
    (fun s => obs ((orderPin d).symm s).1 ((orderPin d).symm s).2) = sign :=
  gather_all_bits d obs sign h

#print axioms actual_individual_request_count
#print axioms with_all_baselines_request_count
#print axioms all_source_calls_at_most_wire_count
#print axioms all_bits_from_decoded_individual_tiles
end
end J7R43Literal