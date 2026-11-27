import LocalTwo
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace GrenetStrict

variable (p : ℕ) [Fact p.Prime]

/-- The valuation subring of the rational numbers at p. -/
def localP : ValuationSubring ℚ := (Rat.padicValuation p).valuationSubring

abbrev D := ↥(localP p)

def toRat : D p →+* ℚ := (localP p).toSubring.subtype

abbrev residue := IsLocalRing.residue (D p)

theorem mem_localP_iff (x : ℚ) :
    x ∈ localP p ↔ 0 ≤ padicValRat p x := by
  rw [localP, Valuation.mem_valuationSubring_iff]
  by_cases hx : x = 0
  · simp [hx]
  · change (if x = 0 then 0 else WithZero.exp (-padicValRat p x)) ≤ 1 ↔ _
    rw [if_neg hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

theorem residue_zero_of_pos (x : D p) (h : 0 < padicValRat p (toRat p x)) :
    residue p x = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  change x ∈ IsLocalRing.maximalIdeal ((Rat.padicValuation p).valuationSubring)
  rw [Valuation.mem_maximalIdeal_iff]
  have hx : (x : ℚ) ≠ 0 := by
    change 0 < padicValRat p (x : ℚ) at h
    intro he
    simp [he] at h
  change (if (x : ℚ) = 0 then 0 else WithZero.exp (-padicValRat p (x : ℚ))) < 1
  rw [if_neg hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  change 0 < padicValRat p (x : ℚ) at h
  omega

/-- Cross-multiplied form of v_p(c) > 1/(p-1). -/
def StrictStep (c : ℚ) : Prop :=
  1 < ((p - 1 : ℕ) : ℤ) * padicValRat p c

omit [Fact (Nat.Prime p)] in
theorem strictStep_ne_zero {c : ℚ} (hc : StrictStep p c) : c ≠ 0 := by
  intro h
  simp [StrictStep, h] at hc

theorem factorial_bound (r : ℕ) (hr : 0 < r) :
    (p-1) * padicValNat p r.factorial ≤ r-1 := by
  have hd : 0 < (Nat.digits p r).sum := by
    have hne := (Nat.digits_ne_nil_iff_ne_zero (b := p)).mpr (Nat.ne_of_gt hr)
    have hh := Nat.getLast_digit_ne_zero p (Nat.ne_of_gt hr)
    have hl : (Nat.digits p r).getLast hne ≤ (Nat.digits p r).sum :=
      List.single_le_sum (fun n _ => Nat.zero_le n) _ (List.getLast_mem hne)
    omega
  have hv := sub_one_mul_padicValNat_factorial (p := p) r
  omega

def kernelRat (c : ℚ) (n : ℕ) : ℚ := c^n / ((n+1).factorial : ℚ)

theorem kernelRat_pos_val (c : ℚ) (hc : StrictStep p c) (n : ℕ) (hn : 0 < n) :
    0 < padicValRat p (kernelRat c n) := by
  have hc0 := strictStep_ne_zero p hc
  have hf0 : ((n+1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  rw [kernelRat, padicValRat.div (pow_ne_zero _ hc0) hf0, padicValRat.pow hc0,
    padicValRat.of_nat]
  have hf := factorial_bound p (n+1) (by omega)
  have hfZ : ((p-1 : ℕ) : ℤ) * (padicValNat p ((n+1).factorial) : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast (show _ ≤ n by simpa using hf)
  have hmul := mul_lt_mul_of_pos_left hc (show (0 : ℤ) < (n : ℤ) by exact_mod_cast hn)
  have hp : 0 < ((p-1 : ℕ) : ℤ) *
      ((n : ℤ) * padicValRat p c - (padicValNat p ((n+1).factorial) : ℤ)) := by
    nlinarith only [hmul, hfZ]
  by_contra! h
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) h)) hp

def kernelCoeff (c : ℚ) (hc : StrictStep p c) (n : ℕ) : D p :=
  ⟨kernelRat c n, (mem_localP_iff p _).mpr (by
    cases n with
    | zero => simp [kernelRat]
    | succ n => exact le_of_lt (kernelRat_pos_val p c hc _ (by omega)))⟩

@[simp] theorem toRat_kernelCoeff (c : ℚ) (hc : StrictStep p c) (n : ℕ) :
    toRat p (kernelCoeff p c hc n) = kernelRat c n := rfl

theorem kernelCoeff_zero (c : ℚ) (hc : StrictStep p c) : kernelCoeff p c hc 0 = 1 := by
  apply Subtype.ext
  change kernelRat c 0 = 1
  simp [kernelRat]

theorem reduce_kernelCoeff (c : ℚ) (hc : StrictStep p c) (n : ℕ) :
    residue p (kernelCoeff p c hc n) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [kernelCoeff_zero]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero _)]
    exact residue_zero_of_pos p _ (kernelRat_pos_val p c hc _ (by omega))

end GrenetStrict

