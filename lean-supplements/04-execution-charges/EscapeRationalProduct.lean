import PinnedCNF
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Section 7's rational product, computed as a signed integer numerator
and a positive factorial denominator. No rational division is needed to
produce the representation or to read the final Boolean count. -/

namespace RootSeparation.EscapeRational

open scoped BigOperators

/-- A prefix of the product `(j - v) / j`, held without intermediate division. -/
def integerProduct (v : ℕ) : ℕ → ℤ × ℕ
  | 0 => (1, 1)
  | j + 1 =>
    let a := integerProduct v j
    (a.1 * ((j + 1 : ℕ) - (v : ℤ)), a.2 * (j + 1))

theorem integer_product_denominator (v j : ℕ) :
    (integerProduct v j).2 = Nat.factorial j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [integerProduct, ih, Nat.factorial_succ, Nat.mul_comm]

theorem integer_product_rational (v j : ℕ) :
    ((integerProduct v j).1 : ℚ) / (integerProduct v j).2 =
      ∏ k ∈ Finset.Icc 1 j, (1 - (v : ℚ) / (k : ℚ)) := by
  induction j with
  | zero => simp [integerProduct]
  | succ j ih =>
    rw [Finset.prod_Icc_succ_top (Nat.succ_pos j)]
    simp only [integerProduct, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Nat.cast_mul]
    rw [← div_mul_div_comm, ih]
    have hk : ((j + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    congr 1
    field_simp

theorem integer_product_den_dvd (v j : ℕ) :
    (∏ k ∈ Finset.Icc 1 j, (1 - (v : ℚ) / (k : ℚ))).den ∣ Nat.factorial j := by
  rw [← integer_product_rational, ← integer_product_denominator v j]
  let z : ℤ := (integerProduct v j).2
  have h := Rat.den_dvd (integerProduct v j).1 z
  rw [Rat.divInt_eq_div] at h
  exact Int.natCast_dvd_natCast.mp h

/-- The working magnitude width for all numerator and denominator prefixes.
An additional sign bit is enough for the signed numerator. -/
def magnitudeWidth (m : ℕ) : ℕ := 1 + m * (m.log2 + 1)

theorem integer_product_prefix_width {v m : ℕ} (hv : v ≤ m) {j : ℕ} (hj : j ≤ m) :
    (integerProduct v j).1.natAbs < 2 ^ magnitudeWidth m ∧
    (integerProduct v j).2 < 2 ^ magnitudeWidth m := by
  have hnum : ∀ k ≤ m, (integerProduct v k).1.natAbs ≤ m ^ k := by
    intro k
    induction k with
    | zero => simp [integerProduct]
    | succ k ih =>
      intro hk
      simp only [integerProduct, Int.natAbs_mul]
      have ha : ((k + 1 : ℕ) - (v : ℤ)).natAbs ≤ m := by omega
      rw [pow_succ]
      exact Nat.mul_le_mul (ih (Nat.le_of_succ_le hk)) ha
  have hp : m ^ j ≤ 2 ^ (m * (m.log2 + 1)) := calc
    m ^ j ≤ (2 ^ (m.log2 + 1)) ^ j :=
      Nat.pow_le_pow_left (Nat.lt_log2_self (n := m)).le _
    _ = 2 ^ ((m.log2 + 1) * j) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (m * (m.log2 + 1)) := by
      apply Nat.pow_le_pow_right (by decide)
      rw [Nat.mul_comm (m.log2 + 1)]
      exact Nat.mul_le_mul_right _ hj
  have hh : 2 ^ (m * (m.log2 + 1)) < 2 ^ magnitudeWidth m := by
    unfold magnitudeWidth
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨((hnum j hj).trans hp).trans_lt hh, ?_⟩
  rw [integer_product_denominator]
  exact ((j.factorial_le_pow.trans (Nat.pow_le_pow_left hj j)).trans hp).trans_lt hh

theorem integer_product_is_original_count {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (σ : V → Bool) :
    let p := integerProduct (PinnedCNF.violations E σ) E.card
    (p.1 : ℚ) / p.2 = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : ℚ) ∧
    (if p.1 = 0 then 0 else 1) = PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  intro p
  have h := integer_product_rational (PinnedCNF.violations E σ) E.card
  rw [← PinnedCNF.count_eq_rational_product] at h
  refine ⟨h, ?_⟩
  have hd : (p.2 : ℚ) ≠ 0 := by
    change (((integerProduct (PinnedCNF.violations E σ) E.card).2 : ℕ) : ℚ) ≠ 0
    rw [integer_product_denominator]
    exact_mod_cast Nat.factorial_ne_zero E.card
  rw [PinnedCNF.count_by_zero_test]
  by_cases hz : PinnedCNF.violations E σ = 0
  · rw [if_pos hz]
    have hp : p.1 ≠ 0 := by
      intro he
      rw [PinnedCNF.count_by_zero_test, if_pos hz, Nat.cast_one] at h
      change (p.1 : ℚ) / p.2 = 1 at h
      simp [he] at h
    exact if_neg hp
  · rw [if_neg hz]
    rw [PinnedCNF.count_by_zero_test, if_neg hz, Nat.cast_zero] at h
    change (p.1 : ℚ) / p.2 = 0 at h
    have he : (p.1 : ℚ) = 0 := (div_eq_zero_iff.mp h).resolve_right hd
    exact if_pos (by exact_mod_cast he)

#print axioms integer_product_denominator
#print axioms integer_product_rational
#print axioms integer_product_den_dvd
#print axioms integer_product_prefix_width
#print axioms integer_product_is_original_count

end RootSeparation.EscapeRational
