import V8CapacitySpecialSignatures
import Mathlib.Algebra.Polynomial.Expand

/-! Residue-precision specialization J6, Frobenius part. The exponent
divisibility is derived over the literal digit polynomial ring. -/
namespace V8CapacitySpecialFrobenius
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures V8CapacitySymbolic

noncomputable section
set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R]
variable {c : ℕ} [ExpChar R c]

theorem power_coeff (hc : 0<c) (f : R[X]) (s j : ℕ) :
    (f^(c^s)).coeff j =
      if c^s∣j then (f.coeff (j/(c^s)))^(c^s) else 0 := by
  rw [← map_expand_pow_char (p:=c),coeff_map,coeff_expand (pow_pos hc s),← iterateFrobenius_eq_pow]
  split_ifs
  · rw [iterateFrobenius_def]
  · exact map_zero _

variable {K H : Type*} [Field K] [Fintype H] {k : ℕ}
variable [ExpChar (MvPolynomial (Digits H k) K) c]

theorem feature_of_scaled_exponents (hc : 0<c) (s : ℕ) (α β : H → ℕ)
    (same : ∀ i, α i=c^s*β i) (j : ℕ) :
    feature (0:K) k α j =
      if c^s∣j then (feature (0:K) k β (j/c^s))^(c^s) else 0 := by
  unfold feature rawFeature
  have hprod :
      (∏ i : H, shiftedPolynomial (MvPolynomial.C (0:K)) k (symInput k i)^α i) =
      (∏ i : H, shiftedPolynomial (MvPolynomial.C (0:K)) k (symInput k i)^β i)^(c^s) := by
    rw [←Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [same i,Nat.mul_comm,pow_mul]
  rw [hprod,power_coeff hc]

theorem feature_below_order_zero (α : H → ℕ) (j : ℕ) (h : j<∑ i : H,α i) :
    feature (0:K) k α j=0 := by
  have hd := feature_dvd (MvPolynomial.C (0:K)) k α j (symInput (R:=K) k)
  change (MvPolynomial.C (0:K))^((∑ i : H, α i)-j)∣feature (0:K) k α j at hd
  rw [map_zero,zero_pow (by omega)] at hd
  exact zero_dvd_iff.mp hd

/-- The necessary support test is exactly j=|alpha|+c^s t; this theorem
does not claim sufficiency when the reduced exponents are all divisible
by c or when there is no available higher jet digit. -/
theorem only_frobenius_offsets (hc : 0<c) (s : ℕ) (α β : H → ℕ)
    (same : ∀ i, α i=c^s*β i) (j : ℕ) (hn : feature (0:K) k α j≠0) :
    ∃ t : ℕ, j=(∑ i : H,α i)+c^s*t := by
  rw [feature_of_scaled_exponents hc s α β same] at hn
  split_ifs at hn with hj
  · obtain ⟨n,hnj⟩ := hj
    have hd := pow_pos hc s
    have div_j : j/c^s=n := by rw [hnj,Nat.mul_div_cancel_left _ hd]
    have hβ : (∑ i : H,β i)≤n := by
      by_contra! h
      rw [div_j,feature_below_order_zero β n h,zero_pow (Nat.ne_of_gt hd)] at hn
      exact hn rfl
    refine ⟨n-(∑ i : H,β i),?_⟩
    rw [hnj]
    simp_rw [same,← Finset.mul_sum,← mul_add,Nat.add_sub_of_le hβ]
  · exact False.elim (hn rfl)

#print axioms power_coeff
#print axioms feature_of_scaled_exponents
#print axioms feature_below_order_zero
#print axioms only_frobenius_offsets
end
end V8CapacitySpecialFrobenius

