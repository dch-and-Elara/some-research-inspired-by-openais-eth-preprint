import J8J9GroupedSigns

/-! Literal tile atlas: one key per occupied (page, parity). The number
of selected moment orders across all occupied tiles is exactly the
number of pins, not the number of pins squared. -/
namespace J9R17AllPins
open scoped Classical BigOperators
open J8Physical
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def tileKey (s : S) : Packet × Fin 2 :=
  ((d.seat (pinWire d s)).1,⟨(d.seat (pinWire d s)).2.val%2,Nat.mod_lt _ (by decide)⟩)

theorem tileKey_eq_iff (s a : S) :
    tileKey d s=tileKey d a ↔ SameTile d (pinWire d s) (pinWire d a) := by
  constructor
  · intro h
    exact ⟨congrArg (fun q : Packet×Fin 2 => q.1) h,congrArg (fun p : Packet×Fin 2 => p.2.val) h⟩
  · intro h
    apply Prod.ext
    · exact h.1
    · exact Fin.ext h.2

abbrev Occupied := {k : Packet×Fin 2 // ∃ s, tileKey d s=k}

def occupiedTile (s : S) : Occupied d := ⟨tileKey d s,⟨s,rfl⟩⟩

def anchor (k : Occupied d) : S := Classical.choose k.prop

theorem anchor_holds (k : Occupied d) : occupiedTile d (anchor d k)=k :=
  Subtype.ext (Classical.choose_spec k.prop)

def tileFiber (k : Occupied d) :
    PinTile d (anchor d k) ≃ {s : S // occupiedTile d s=k} where
  toFun s := ⟨s.val,(Subtype.ext ((tileKey_eq_iff d _ _).2 s.prop)).trans (anchor_holds d k)⟩
  invFun s := ⟨s.val,(tileKey_eq_iff d _ _).1
    (congrArg Subtype.val (s.prop.trans (anchor_holds d k).symm))⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable [Fintype S] [Fintype Packet] [DecidableEq Packet]
abbrev Orders := Σ k : Occupied d, Fin (Fintype.card (PinTile d (anchor d k)))

/-- Same physical pin, indexed once by its tile and actual binary-position rank. -/
def orderPin : Orders d ≃ S :=
  (Equiv.sigmaCongrRight (fun k => (pinEnumeration d (anchor d k)).trans (tileFiber d k))).trans
    (Equiv.sigmaFiberEquiv (occupiedTile d))

theorem orderPin_exact (j : Orders d) :
    orderPin d j = (pinEnumeration d (anchor d j.1) j.2).val := rfl

theorem moment_orders_count : Fintype.card (Orders d) = Fintype.card S :=
  Fintype.card_congr (orderPin d)

theorem completed_gather_count (M : ℕ) :
    Fintype.card (Orders d × Fin (10*M+1)) = Fintype.card S*(10*M+1) := by
  rw [Fintype.card_prod,moment_orders_count,Fintype.card_fin]

theorem group_receipt_count (M : ℕ) :
    Fintype.card ((Orders d × Fin (10*M+1)) × Fin 64) = Fintype.card S*(10*M+1)*64 := by
  rw [Fintype.card_prod,completed_gather_count,Fintype.card_fin]

include d in
theorem pin_card_le_wire_card [Fintype R] :
    Fintype.card S ≤ Fintype.card (Wire R) := by
  apply Fintype.card_le_of_injective (pinWire d)
  intro s j h
  have h' := congrArg d.column h
  rw [pinWire_column,pinWire_column] at h'
  exact Sum.inl.inj h'

theorem gather_count_quadratic [Fintype R] (M : ℕ) (idx : Wire R ≃ Fin M) :
    Fintype.card (Orders d × Fin (10*M+1)) ≤ M*(10*M+1) := by
  rw [completed_gather_count]
  apply Nat.mul_le_mul_right
  rw [← Fintype.card_fin M,← Fintype.card_congr idx]
  exact pin_card_le_wire_card d

/-- A decoded tile vector really recovers all pins of the original source. -/
theorem gather_all_bits (obs : ∀ k : Occupied d, Fin (Fintype.card (PinTile d (anchor d k))) → Bool)
    (sign : S→Bool)
    (h : ∀ k i, obs k i=sign (pinEnumeration d (anchor d k) i).val) :
    (fun s => obs ((orderPin d).symm s).1 ((orderPin d).symm s).2) = sign := by
  funext s
  rw [h,← orderPin_exact,Equiv.apply_symm_apply]

#print axioms tileKey_eq_iff
#print axioms tileFiber
#print axioms orderPin_exact
#print axioms moment_orders_count
#print axioms completed_gather_count
#print axioms group_receipt_count
#print axioms gather_all_bits
#print axioms pin_card_le_wire_card
#print axioms gather_count_quadratic
end
end J9R17AllPins