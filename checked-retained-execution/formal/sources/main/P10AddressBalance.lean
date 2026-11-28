import P10TripleUnion

/-! Exact density of eligible ordered cells at one coordinate. We count
an explicit uniformly padded array, not a probabilistic approximation. -/

namespace P10AddressBalance

variable {C : Type*}

theorem diagonal_card (r : ℕ) :
    Nat.card {a : Fin r × Fin r // a.1 = a.2} = r := by
  let e : {a : Fin r × Fin r // a.1 = a.2} ≃ Fin r :=
    { toFun := fun a => a.val.1
      invFun := fun i => ⟨(i,i),rfl⟩
      left_inv := by rintro ⟨⟨i,j⟩,h⟩; cases h; rfl
      right_inv := by intro i; rfl }
  rw [Nat.card_congr e, Nat.card_fin]

theorem unequal_card (r : ℕ) :
    Nat.card {a : Fin r × Fin r // a.1 ≠ a.2} = r*(r-1) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_prod]
  have hd := diagonal_card r
  rw [Nat.card_eq_fintype_card] at hd
  rw [hd]
  simp only [Fintype.card_fin]
  rw [Nat.mul_sub, Nat.mul_one]

/-- Other coordinates and uniformly filled seats multiply the diagonal
and off-diagonal counts by exactly the same factor. -/
theorem padded_cell_ratio (r H : ℕ) :
    r * Nat.card ({a : Fin r × Fin r // a.1 ≠ a.2} × C × Fin H) =
      (r-1) * Nat.card ((Fin r × Fin r) × C × Fin H) := by
  simp only [Nat.card_prod, unequal_card, Nat.card_fin]
  ring

theorem full_layout_exponent (r q B M H eligible total : ℕ)
    (hr : 0 < r) (hq : 2 ≤ q) (hB : 0 < B)
    (hf : 3*(q*B)*eligible = Nat.card ({a : Fin r × Fin r // a.1 ≠ a.2} × C × Fin H))
    (ht : M = Nat.card ((Fin r × Fin r) × C × Fin H))
    (hM : M = 3*(q*B)*total) :
    ((eligible*(q*B-2*B) : ℕ) : ℚ) =
      (1-1/(r:ℚ))/3*(1-4/(2*(q:ℚ)))*M := by
  have h := padded_cell_ratio (C:=C) r H
  rw [← hf, ← ht, hM] at h
  have hprod : 3*(q*B) * (r*eligible) = 3*(q*B) * ((r-1)*total) := by
    calc
      _ = r*(3*(q*B)*eligible) := by ring
      _ = _ := h
      _ = _ := by ring
  exact P10TripleUnion.exponent_matches r q B M eligible total hr hq
    (Nat.eq_of_mul_eq_mul_left (by positivity) hprod) hM

#print axioms diagonal_card
#print axioms unequal_card
#print axioms padded_cell_ratio
#print axioms full_layout_exponent

end P10AddressBalance