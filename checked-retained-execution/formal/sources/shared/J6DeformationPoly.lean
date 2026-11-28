import J6NativeHeightKernel
import Mathlib.Algebra.Polynomial.BigOperators

namespace J6DeformationPoly
open scoped Classical BigOperators Polynomial
open P1DyadicGrid Polynomial

variable {R P : Type*} [CommRing R] [Algebra ℚ R] [Fintype P]

/-- The cancelled source Cauchy entry as a polynomial, not rational
evaluation at a denominator that might be zero. -/
noncomputable def entry (R : Type*) [CommRing R] [Algebra ℚ R]
    (a : ℕ) (k : ℤ) : R[X] :=
  C (algebraMap ℚ R ((((cauchyPolynomial a).derivative.eval 0 : ℤ) : ℚ)⁻¹)) *
      ∏ q ∈ (grid a).erase k, (X - C (q : R))

theorem grid_card (a : ℕ) : (grid a).card = 2 * 2^a := by
  simp only [grid, Int.card_Ico, sub_neg_eq_add]
  have hp : 0 ≤ pow₂ a := (pow₂_pos a).le
  rw [Int.toNat_add hp hp]
  simp only [pow₂, Int.toNat_pow_of_nonneg (by norm_num : (0:ℤ) ≤ 2)]
  rw [show Int.toNat (2:ℤ) = 2 from rfl, two_mul]

omit [Fintype P] in
theorem degree_entry (a : ℕ) (k : ℤ) (hk : k ∈ grid a) :
    (entry R a k).natDegree ≤ 2 * 2^a - 1 := by
  unfold entry
  apply (natDegree_mul_le (p := C (algebraMap ℚ R _))).trans
  simp only [natDegree_C, zero_add]
  apply (natDegree_prod_le _ _).trans
  calc
    (∑ q ∈ (grid a).erase k, (X - C (q:R) : R[X]).natDegree) ≤
        ∑ _q ∈ (grid a).erase k, 1 := by
      exact Finset.sum_le_sum (fun q _ => natDegree_X_sub_C_le (q : R))
    _ = _ := by simp [Finset.card_erase_of_mem hk, grid_card]

/-- Slot addresses and packet membership are taken from the current call.
The zero-outside-packet condition is built into the definition. -/
noncomputable def matrix {K : Type*} [DecidableEq K]
    (page : P → K) (slot : P → ℤ) (a : ℕ) (i j : P) : R[X] :=
  if page i = page j then entry R a (slot j - slot i) else 0

noncomputable def network {K : Type*} [DecidableEq K]
    (page : P → K) (slot : P → ℤ) (a : ℕ)
    (A B : (P → Bool) → R) : R[X] :=
  ∑ Y : P → Bool, ∑ Xb : P → Bool, C (A Y * B Xb) *
    ∏ i, let z := ∑ j, if Xb j then matrix page slot a i j else 0
         if Y i then z else 1 - z

theorem network_degree {K : Type*} [DecidableEq K]
    (page : P → K) (slot : P → ℤ) (a : ℕ) (A B : (P → Bool) → R)
    (hslot : ∀ i j, page i = page j → slot j-slot i ∈ grid a) :
    (network page slot a A B).natDegree ≤ Fintype.card P * (2 * 2^a - 1) := by
  classical
  unfold network
  apply natDegree_sum_le_of_forall_le
  intro Y _
  apply natDegree_sum_le_of_forall_le
  intro Xb _
  apply (natDegree_mul_le (p := C (A Y * B Xb))).trans
  simp only [natDegree_C,zero_add]
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : P, (2 * 2^a - 1) := by
      apply Finset.sum_le_sum
      intro i _
      let z : R[X] := ∑ j, if Xb j then matrix page slot a i j else 0
      change (if Y i then z else 1-z).natDegree ≤ _
      have hz : z.natDegree ≤ 2 * 2^a - 1 := by
        apply natDegree_sum_le_of_forall_le
        intro j _
        by_cases hx : Xb j = true
        · by_cases h : page i = page j
          · simpa only [hx, if_true, matrix, if_pos h] using degree_entry (R:=R) a _ (hslot i j h)
          · simp [hx,matrix,h]
        · simp [hx]
      by_cases hY : Y i = true
      · simp [hY,hz]
      · rw [if_neg hY]
        exact (natDegree_sub_le 1 z).trans (max_le (by simp) hz)
    _ = _ := by simp

#print axioms grid_card
#print axioms degree_entry
#print axioms network_degree
end J6DeformationPoly
