import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# J7 layout: exact finite biased-label law

For a single pin gadget, draw the pin symbol uniformly, draw the subdivision
symbol uniformly outside it, and then give its private clone symbol equality
probability 2/r. Although the pin edge alone forbids diagonal cells, the
combined expected contribution of the two edges is uniform over all ordered
cells. This does not model the full conditional-expectation placement routine.
-/

open scoped BigOperators Classical

namespace NativeLabelLaw

noncomputable section

variable {A : Type*} [Fintype A]

def qSize (A : Type*) [Fintype A] : ℚ := Fintype.card A

def rowKernel (pin row : A) : ℚ :=
  if row = pin then 0 else 1 / (qSize A - 1)

def cloneKernel (row clone : A) : ℚ :=
  if clone = row then 2 / qSize A else
    (qSize A - 2) / (qSize A * (qSize A - 1))

def pinPair (row pin : A) : ℚ := (1 / qSize A) * rowKernel pin row

def tripleMass (pin row clone : A) : ℚ :=
  pinPair row pin * cloneKernel row clone

private theorem qSize_ge_two (h : 2 ≤ Fintype.card A) : 2 ≤ qSize A := by
  unfold qSize
  exact_mod_cast h

private theorem qSize_pos (h : 2 ≤ Fintype.card A) : 0 < qSize A :=
  lt_of_lt_of_le (by norm_num) (qSize_ge_two h)

private theorem qSize_sub_one_pos (h : 2 ≤ Fintype.card A) : 0 < qSize A - 1 := by
  have hh := qSize_ge_two h
  linarith

private theorem sum_diagonal (h : 2 ≤ Fintype.card A) (a : A) (diagonal other : ℚ) :
    (∑ b : A, if b = a then diagonal else other) =
      diagonal + (qSize A - 1) * other := by
  classical
  have hs : (Finset.univ.erase a).card = Fintype.card A - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  calc
    _ = (if a = a then diagonal else other) +
        ∑ b ∈ Finset.univ.erase a, if b = a then diagonal else other :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)).symm
    _ = diagonal + ∑ _b ∈ Finset.univ.erase a, other := by
      rw [if_pos rfl]
      congr 1
      exact Finset.sum_congr rfl fun b hb => if_neg (Finset.ne_of_mem_erase hb)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hs, Nat.cast_sub (by omega)]
      rfl

theorem rowKernel_normalized (h : 2 ≤ Fintype.card A) (pin : A) :
    (∑ s : A, rowKernel pin s) = 1 := by
  unfold rowKernel
  rw [sum_diagonal h, zero_add]
  simpa only [mul_div_assoc] using
    mul_div_cancel_left₀ (1 : ℚ) (ne_of_gt (qSize_sub_one_pos h))

theorem cloneKernel_normalized (h : 2 ≤ Fintype.card A) (row : A) :
    (∑ b : A, cloneKernel row b) = 1 := by
  unfold cloneKernel
  rw [sum_diagonal h]
  field_simp [ne_of_gt (qSize_pos h), ne_of_gt (qSize_sub_one_pos h)]
  ring

theorem tripleMass_nonnegative (h : 2 ≤ Fintype.card A) (pin row clone : A) :
    0 ≤ tripleMass pin row clone := by
  have hr := (qSize_pos h).le
  have hsub := (qSize_sub_one_pos h).le
  have ht : 0 ≤ qSize A - 2 := sub_nonneg.mpr (qSize_ge_two h)
  apply mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hr) ?_) ?_
  · unfold rowKernel
    split
    · exact le_rfl
    · exact div_nonneg (by norm_num) hsub
  · unfold cloneKernel
    split
    · exact div_nonneg (by norm_num) hr
    · exact div_nonneg ht (mul_nonneg hr hsub)

/-- Marginal on the first physical wire. -/
theorem joint_pin_edge (h : 2 ≤ Fintype.card A) (row pin : A) :
    (∑ b : A, tripleMass pin row b) = pinPair row pin := by
  simp only [tripleMass, ← Finset.mul_sum, cloneKernel_normalized h, mul_one]

/-- The first row symbol is uniform, even though its conditional draw
excludes the already fixed pin symbol. -/
theorem row_symbol_uniform (h : 2 ≤ Fintype.card A) (row : A) :
    (∑ a : A, pinPair row a) = 1 / qSize A := by
  simp_rw [pinPair, ← Finset.mul_sum]
  have hs : (∑ a : A, rowKernel a row) = 1 := by
    simpa only [rowKernel, eq_comm] using rowKernel_normalized h row
  rw [hs, mul_one]

theorem pin_symbol_uniform (h : 2 ≤ Fintype.card A) (pin : A) :
    (∑ s : A, ∑ b : A, tripleMass pin s b) = 1 / qSize A := by
  simp only [joint_pin_edge h, pinPair, ← Finset.mul_sum, rowKernel_normalized h, mul_one]

/-- Marginal on the second physical wire. -/
theorem joint_clone_edge (h : 2 ≤ Fintype.card A) (row clone : A) :
    (∑ a : A, tripleMass a row clone) = (1 / qSize A) * cloneKernel row clone := by
  simp only [tripleMass, ← Finset.sum_mul, row_symbol_uniform h]

theorem clone_symbol_uniform (h : 2 ≤ Fintype.card A) (clone : A) :
    (∑ s : A, ∑ a : A, tripleMass a s clone) = 1 / qSize A := by
  simp_rw [joint_clone_edge h, ← Finset.mul_sum]
  have hs : (∑ s : A, cloneKernel s clone) = 1 := by
    simpa only [cloneKernel, eq_comm] using cloneKernel_normalized h clone
  rw [hs, mul_one]

theorem tripleMass_normalized (h : 2 ≤ Fintype.card A) :
    (∑ a : A, ∑ s : A, ∑ b : A, tripleMass a s b) = 1 := by
  simp only [pin_symbol_uniform h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change qSize A * (1 / qSize A) = 1
  simpa only [mul_div_assoc] using
    mul_div_cancel_left₀ (1 : ℚ) (ne_of_gt (qSize_pos h))

theorem pinPair_closed (row pin : A) :
    pinPair row pin = if row = pin then 0 else 1 / (qSize A * (qSize A - 1)) := by
  by_cases hr : row = pin
  · simp [pinPair, rowKernel, hr]
  · simp [pinPair, rowKernel, hr, mul_comm]

/-- J7 layout's exact per-cell load identity: an ordered cell sees expected
total 2/r² from the gadget's two original physical wires. -/
theorem combined_cell_load (h : 2 ≤ Fintype.card A) (row label : A) :
    (∑ b : A, tripleMass label row b) + (∑ a : A, tripleMass a row label) =
      2 / (qSize A) ^ 2 := by
  rw [joint_pin_edge h, joint_clone_edge h, pinPair_closed]
  have hr := ne_of_gt (qSize_pos h)
  have hs := ne_of_gt (qSize_sub_one_pos h)
  by_cases he : row = label
  · subst label
    simp [cloneKernel, pow_two]
    field_simp [hr]
  · simp [cloneKernel, he, Ne.symm he]
    field_simp [hr, hs]
    ring

/-- Exact conditional pin-event mass when the old pin symbol is already
fixed. The clone label is summed out, not observed. -/
theorem pin_event_given_pin (h : 2 ≤ Fintype.card A) (old row pin : A) :
    (∑ s : A, ∑ b : A,
      if s = row ∧ old = pin then rowKernel old s * cloneKernel s b else 0) =
        if old = pin then rowKernel old row else 0 := by
  by_cases he : old = pin
  · simp only [he, and_true, ↓reduceIte]
    have hh (s : A) : (∑ b : A, if s = row then rowKernel pin s * cloneKernel s b else 0) =
        if s = row then rowKernel pin s else 0 := by
      by_cases hs : s = row <;> simp [hs, ← Finset.mul_sum, cloneKernel_normalized h]
    simp_rw [hh]
    simp
  · simp [he]

/-- With a prescribed vector of pin symbols (even with ties), the expected
pin-only load of the cell equals the number of pins with the prescribed
column symbol times its exact conditional row-event mass. -/
theorem conditional_pin_count {P : Type*} [Fintype P] (h : 2 ≤ Fintype.card A)
    (old : P → A) (row pin : A) :
    (∑ v : P, ∑ s : A, ∑ b : A,
      if s = row ∧ old v = pin then rowKernel (old v) s * cloneKernel s b else 0) =
      ((Finset.univ.filter fun v : P => old v = pin).card : ℚ) * rowKernel pin row := by
  simp_rw [pin_event_given_pin h]
  have hh (v : P) : (if old v = pin then rowKernel (old v) row else 0) =
      if old v = pin then rowKernel pin row else 0 := by
    by_cases hv : old v = pin <;> simp [hv]
  simp_rw [hh, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Unconditional first-wire load on a finite family; joint independence
between gadgets is never used. -/
theorem pin_only_expected_count {P : Type*} (s : Finset P) (h : 2 ≤ Fintype.card A)
    (row pin : A) :
    (∑ _v ∈ s, ∑ b : A, tripleMass pin row b) =
      if row = pin then 0 else (s.card : ℚ) / (qSize A * (qSize A - 1)) := by
  rw [Finset.sum_const, joint_pin_edge h, pinPair_closed, nsmul_eq_mul]
  by_cases hr : row = pin
  · simp only [if_pos hr, mul_zero]
  · simp only [if_neg hr, ← mul_div_assoc, mul_one]

#print axioms rowKernel_normalized
#print axioms cloneKernel_normalized
#print axioms tripleMass_nonnegative
#print axioms tripleMass_normalized
#print axioms row_symbol_uniform
#print axioms pin_symbol_uniform
#print axioms clone_symbol_uniform
#print axioms combined_cell_load
#print axioms pin_event_given_pin
#print axioms conditional_pin_count
#print axioms pin_only_expected_count

end

end NativeLabelLaw
