import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

namespace SharpDifference

instance twoPrimeFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The rational 2-adic valuation ring, identified below by reduced denominators. -/
def localTwo : ValuationSubring ℚ :=
  (Rat.padicValuation 2).valuationSubring

abbrev D := ↥localTwo

def toRat : D →+* ℚ := localTwo.toSubring.subtype

theorem mem_localTwo_iff_val (q : ℚ) : q ∈ localTwo ↔ 0 ≤ padicValRat 2 q := by
  rw [localTwo, Valuation.mem_valuationSubring_iff]
  by_cases hq : q = 0
  · simp [hq]
  · change (if q = 0 then 0 else WithZero.exp (-padicValRat 2 q)) ≤ 1 ↔ _
    rw [if_neg hq, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

theorem mem_localTwo_iff_odd_den (q : ℚ) : q ∈ localTwo ↔ Odd q.den := by
  rw [mem_localTwo_iff_val, ← Nat.not_even_iff_odd, even_iff_two_dvd, padicValRat_def]
  by_cases hd : 2 ∣ q.den
  · have hn : ¬ (2 : ℤ) ∣ q.num := by
      intro h
      have ha : 2 ∣ q.num.natAbs := by
        simpa using Int.natAbs_dvd_natAbs.mpr h
      have := Nat.eq_one_of_dvd_coprimes q.reduced ha hd
      omega
    have hden := one_le_padicValNat_of_dvd q.den_ne_zero hd
    rw [padicValInt.eq_zero_of_not_dvd hn]
    omega
  · simp [hd, padicValNat.eq_zero_of_not_dvd hd]

theorem factorial_val_two_le (r : ℕ) (hr : 0 < r) :
    padicValNat 2 r.factorial ≤ r - 1 := by
  have hdigit : 0 < (Nat.digits 2 r).sum := by
    have hne := (Nat.digits_ne_nil_iff_ne_zero (b := 2)).mpr (Nat.ne_of_gt hr)
    have hl := Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hr)
    have hle : (Nat.digits 2 r).getLast hne ≤ (Nat.digits 2 r).sum :=
      List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getLast_mem hne)
    omega
  have h := sub_one_mul_padicValNat_factorial (p := 2) r
  norm_num at h
  omega

/-- The power of two in the numerator cancels every factor of two in the factorial. -/
theorem scaled_factorial_mem (r : ℕ) (hr : 0 < r) :
    (2 : ℚ) ^ (r - 1) / (r.factorial : ℚ) ∈ localTwo := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hf : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hv : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide)
  have hbound := factorial_val_two_le r hr
  rw [mem_localTwo_iff_val, padicValRat.div (pow_ne_zero _ h2) hf,
    padicValRat.pow h2, hv, mul_one, padicValRat.of_nat]
  omega

theorem scaled_factorial_odd_den (r : ℕ) (hr : 0 < r) :
    Odd (((2 : ℚ) ^ (r - 1) / (r.factorial : ℚ)).den) :=
  (mem_localTwo_iff_odd_den _).mp (scaled_factorial_mem r hr)

/-- The coefficient of degree r+1 after the scalar c has been removed. -/
def scaledFactorial (r : ℕ) : D :=
  ⟨(2 : ℚ) ^ r / ((r + 1).factorial : ℚ),
    by simpa using scaled_factorial_mem (r + 1) (Nat.succ_pos r)⟩

@[simp] theorem toRat_scaledFactorial (r : ℕ) :
    toRat (scaledFactorial r) = (2 : ℚ) ^ r / ((r + 1).factorial : ℚ) := rfl

end SharpDifference

