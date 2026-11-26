
import S11Interpolation
import S11Schedule
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section
namespace S11

open Polynomial
open scoped BigOperators

variable {K W P : Type*} [Field K] [CharZero K]

def grid (L : ℕ) : Finset ℤ := Finset.Ico (-(L : ℤ)) L

theorem grid_card (L : ℕ) : (grid L).card = 2*L := by
  simp [grid, Int.card_Ico]
  omega

def originDenominator (K : Type*) [Field K] (L : ℕ) : K :=
  ∏ q ∈ (grid L).erase 0, -(q : K)

/-- The polynomial obtained by cancelling the single grid factor at y-x
    in the Appendix D packet kernel. -/
def packetKernel (K : Type*) [Field K] (L : ℕ) (x y : Fin L) : K[X] :=
  C (originDenominator K L)⁻¹ *
    ∏ q ∈ (grid L).erase ((y : ℤ) - (x : ℤ)), (X - C (q : K))

private theorem difference_in_grid {L : ℕ} (x y : Fin L) :
    (y : ℤ) - (x : ℤ) ∈ grid L := by
  simp only [grid, Finset.mem_Ico]
  have hx := x.isLt
  have hy := y.isLt
  omega

omit [CharZero K] in
theorem packetKernel_degree {L : ℕ} (x y : Fin L) :
    (packetKernel K L x y).natDegree ≤ 2*L-1 := by
  unfold packetKernel
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  calc
    _ ≤ ∑ _ ∈ (grid L).erase ((y : ℤ) - (x : ℤ)), (1 : ℕ) :=
      Finset.sum_le_sum fun q _ => natDegree_X_sub_C_le (q : K)
    _ = _ := by simp [Finset.card_erase_of_mem (difference_in_grid x y), grid_card]

theorem packetKernel_zero {L : ℕ} (x y : Fin L) :
    (packetKernel K L x y).eval 0 = if x = y then 1 else 0 := by
  classical
  have hL := x.isLt
  have h0 : (0 : ℤ) ∈ grid L := by simp [grid]; omega
  by_cases h : x = y
  · subst y
    have hn : originDenominator K L ≠ 0 := by
      apply Finset.prod_ne_zero_iff.2
      intro q hq
      have hnq := (Finset.mem_erase.1 hq).1
      simpa using hnq
    simp only [packetKernel, sub_self, eval_mul, eval_C, eval_prod, eval_sub, eval_X, zero_sub,
      if_true]
    exact inv_mul_cancel₀ hn
  · have hd : (y : ℤ) - (x : ℤ) ≠ 0 := by
      intro hz
      apply h
      apply Fin.ext
      omega
    have hp : (∏ q ∈ (grid L).erase ((y : ℤ)-(x : ℤ)), (-(q : K))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hd, h0⟩)
      simp
    simp only [packetKernel, eval_mul, eval_C, eval_prod, eval_sub, eval_X, zero_sub, if_neg h]
    rw [hp, mul_zero]

variable [Fintype W] [DecidableEq W] [DecidableEq P]

/-- Restrict the packet kernel to real ports. Identical wire positions
    on both sides encode the original wire identification. -/
def kernel {L : ℕ} (position : W ↪ P × Fin L) (x y : W) : K[X] :=
  if (position x).1 = (position y).1 then
    packetKernel K L (position x).2 (position y).2 else 0

omit [Fintype W] in
theorem kernel_zero {L : ℕ} (position : W ↪ P × Fin L) (x y : W) :
    (kernel position x y : K[X]).eval 0 = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp [kernel, packetKernel_zero]
  · by_cases hp : (position x).1 = (position y).1
    · have hn : (position x).2 ≠ (position y).2 := fun he =>
        h (position.injective (Prod.ext hp he))
      simp [kernel, hp, hn, h, packetKernel_zero]
    · simp [kernel, hp, h]

def literalPoly (b : Bool) (f : K[X]) : K[X] := if b then f else 1-f

/-- Equation D's deformed contraction, with A and B the products of the
    lifted old tensors on the respective sides. -/
def deformed (A B : (W → Bool) → K) {L : ℕ} (place : W ↪ P × Fin L) : K[X] :=
  ∑ Xb : W → Bool, ∑ Yb : W → Bool, C (A Yb * B Xb) *
    ∏ x, literalPoly (Yb x) (∑ y, kernel place x y * C ((Xb y).toNat : K))

theorem deformed_degree (A B : (W → Bool) → K)
    {L : ℕ} (place : W ↪ P × Fin L) :
    (deformed A B place).natDegree ≤ Fintype.card W * (2*L-1) := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro xb _
  apply natDegree_sum_le_of_forall_le
  intro yb _
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  have hc : (∑ _ : W, (2*L-1)) = Fintype.card W * (2*L-1) := by simp
  rw [← hc]
  apply Finset.sum_le_sum
  intro x _
  have h : (∑ y, kernel place x y * C ((xb y).toNat : K)).natDegree ≤ 2*L-1 := by
    apply natDegree_sum_le_of_forall_le
    intro y _
    apply (natDegree_mul_C_le _ _).trans
    unfold kernel
    split
    · apply packetKernel_degree
    · simp
  cases hx : yb x
  · simp only [literalPoly, Bool.false_eq_true, if_false]
    exact (natDegree_sub_le _ _).trans (by simpa using h)
  · simpa only [literalPoly, hx, if_true] using h

private theorem eval_linear_form {L : ℕ} (place : W ↪ P × Fin L)
    (b : W → Bool) (x : W) :
    (eval (0 : K)) (∑ y, kernel place x y * C ((b y).toNat : K)) = ((b x).toNat : K) := by
  classical
  simp [eval_finset_sum, eval_mul, kernel_zero]

theorem deformed_origin (A B : (W → Bool) → K)
    {L : ℕ} (place : W ↪ P × Fin L) :
    (deformed A B place).eval 0 = ∑ b : W → Bool, A b * B b := by
  classical
  simp only [deformed, eval_finset_sum, eval_mul, eval_C, eval_prod]
  apply Finset.sum_congr rfl
  intro xb _
  rw [Finset.sum_eq_single xb]
  · have h (x : W) :
        (literalPoly (xb x) (∑ y, kernel place x y * C ((xb y).toNat : K))).eval 0 = 1 := by
      unfold literalPoly
      cases hx : xb x <;> simp only [Bool.false_eq_true, if_false, if_true, eval_sub,
        eval_one, eval_linear_form, hx, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero,
        Nat.cast_one, sub_zero]
    simp only [h, Finset.prod_const_one, mul_one]
  · intro yb _ hne
    obtain ⟨x,hx⟩ : ∃ x, yb x ≠ xb x := by
      by_contra! h
      exact hne (funext h)
    have h : (literalPoly (yb x) (∑ y, kernel place x y * C ((xb y).toNat : K))).eval 0 = 0 := by
      unfold literalPoly
      cases hy : yb x <;> cases hb : xb x <;>
        simp only [hy, hb, Bool.false_eq_true, if_false, if_true, eval_sub, eval_one,
          eval_linear_form, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one,
          sub_self] at hx ⊢ <;> first | exact hx rfl | trivial
    rw [Finset.prod_eq_zero (Finset.mem_univ x) h, mul_zero]
  · simp

omit [CharZero K] in
theorem local_degree_bound (F : K[X]) (d : ℕ) (hF : F.natDegree ≤ d) (t α : K) :
    (F.comp (C t + C α * X)).degree < ↑(d+1) := by
  refine degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.2
    (show (F.comp (C t + C α * X)).natDegree < d+1 from ?_))
  have hl : (C t + C α * X).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (by simpa using natDegree_C_mul_X_pow_le α 1)
  have hd := (natDegree_comp_le (p := F) (q := C t + C α * X)).trans (Nat.mul_le_mul hF hl)
  omega

#print axioms packetKernel_degree
#print axioms packetKernel_zero
#print axioms kernel_zero
#print axioms deformed_degree
#print axioms deformed_origin
#print axioms local_degree_bound

end S11

