import SourceDensity

/-! A positive integral full-cell load forces an upper bound on the number
of possible cells. For paired labels this bounds the full coordinate count
directly, independently of a chosen parameter schedule. -/

namespace SourceCoordinates

variable {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]

/-- A single occupied cell bounds the size of the full alphabet of cells. -/
theorem card_cells_le_twice_ports (cell : P → C) (port : P) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate cell Δ) : Fintype.card C ≤ 2 * Fintype.card P := by
  letI : Nonempty C := ⟨cell port⟩
  have hload : 1 ≤ SourceDensity.fiberCount cell (cell port) := by
    change 0 < (Finset.univ.filter fun p : P => cell p = cell port).card
    exact Finset.card_pos.mpr ⟨port, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hloadQ : (1 : ℚ) ≤ SourceDensity.fiberCount cell (cell port) := by exact_mod_cast hload
  have hcardQ : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have h := (le_div_iff₀ hcardQ).1 (hloadQ.trans (SourceDensity.port_cell_bound cell Δ cert (cell port)))
  rw [one_mul] at h
  exact_mod_cast h

theorem paired_alphabet_lower (k r : ℕ) (hk : 0 < k) (hr : 27 ≤ r) :
    20 * 2 ^ k ≤ (r ^ k) * (r ^ k) := by
  have hbase : 40 ≤ r * r := le_trans (by decide : 40 ≤ 27 * 27) (Nat.mul_le_mul hr hr)
  have h20 : 20 ≤ 20 ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 20) hk
  calc
    _ ≤ 20 ^ k * 2 ^ k := Nat.mul_le_mul_right _ h20
    _ = 40 ^ k := by rw [← mul_pow, show (20 : ℕ) * 2 = 40 by decide]
    _ ≤ (r * r) ^ k := Nat.pow_le_pow_left hbase k
    _ = _ := mul_pow r r k

variable {V I A : Type*} [Fintype V] [Nonempty V] [Fintype I] [DecidableEq I]
variable [Fintype A] [DecidableEq A]

/-- Every full coordinate already fits the binary logarithmic budget. -/
theorem coordinate_count_le_log (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate cell Δ) (hports : Fintype.card P = 10 * Fintype.card V)
    (hA : 27 ≤ Fintype.card A) (hI : 0 < Fintype.card I) :
    Fintype.card I ≤ (Fintype.card V).log2 := by
  classical
  let v := Classical.choice (inferInstance : Nonempty V)
  have h := card_cells_le_twice_ports cell (pin v) Δ cert
  rw [Fintype.card_prod, Fintype.card_fun, hports] at h
  have hraw := (paired_alphabet_lower _ _ hI hA).trans h
  have hscaled : 20 * 2 ^ Fintype.card I ≤ 20 * Fintype.card V := by
    simpa only [← Nat.mul_assoc] using hraw
  exact (Nat.le_log2 Fintype.card_ne_zero).2 (Nat.le_of_mul_le_mul_left hscaled (by decide))

theorem kept_card_le_log (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate cell Δ) (hports : Fintype.card P = 10 * Fintype.card V)
    (hA : 27 ≤ Fintype.card A) (kept : Finset I) (hkept : kept.Nonempty) :
    kept.card ≤ (Fintype.card V).log2 :=
  (Finset.card_le_univ kept).trans <|
    coordinate_count_le_log pin cell Δ cert hports hA
      (hkept.card_pos.trans_le (Finset.card_le_univ kept))

#print axioms card_cells_le_twice_ports
#print axioms paired_alphabet_lower
#print axioms coordinate_count_le_log
#print axioms kept_card_le_log

end SourceCoordinates
