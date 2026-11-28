import J7ToJ8Incidence

/-! # Direct two-leg subdivision indexing -/

namespace J7ToJ8Canonical

/-- Modeling the physical converter's two legs per ordinary subdivision
by the product with Bool discharges the row-cardinality hypothesis. -/
def directRowFiber {Row : Type*} (r : Row) :
    {w : Row × Bool // w.1 = r} ≃ Bool where
  toFun w := w.val.2
  invFun b := ⟨(r,b),rfl⟩
  left_inv := by
    rintro ⟨⟨q,b⟩,h⟩
    change q = r at h
    subst q
    rfl
  right_inv _ := rfl

theorem ordinary_row_exact_two {Row : Type*} (r : Row) :
    Nat.card {w : Row × Bool // w.1 = r} = 2 := by
  rw [Nat.card_congr (directRowFiber r), Nat.card_eq_fintype_card, Fintype.card_bool]

/-- In this explicit incidence encoding the witnesses are on the original
ports: the two old private gadget wires, or exactly one occurrence per
indexed leg of an ordinary subdivision. -/
noncomputable def directRowWire (Pair Row : Type*) :
    J8Physical.Wire (J7ToJ8Incidence.Subdivision Pair Row) ≃ J7SourceLabels.Wire Pair (Row × Bool) :=
  J7ToJ8Incidence.rowWire Prod.fst ordinary_row_exact_two

theorem directRowWire_preserves (Pair Row : Type*) (w : J8Physical.Wire (J7ToJ8Incidence.Subdivision Pair Row)) :
    J7SeatSource.rowNode Prod.fst (directRowWire Pair Row w) = w.1 :=
  J7ToJ8Incidence.rowWire_owner Prod.fst ordinary_row_exact_two w

#print axioms ordinary_row_exact_two
#print axioms directRowWire_preserves

end J7ToJ8Canonical
