import LayoutBudget
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace Reconstruction.LayoutMismatch
open Polynomial
open scoped Polynomial
noncomputable section

abbrev Mask (I : Type*) := I → Bool
abbrev Word (I : Type*) := I → ℚ × ℚ

def ones {I : Type*} [Fintype I] (s : Mask I) : Finset I :=
  Finset.univ.filter (fun i => s i = true)

def weight {I : Type*} [Fintype I] (s : Mask I) : ℕ := (ones s).card

def dualMask {I : Type*} (w : Word I) (s : Mask I) : Mask I :=
  fun i => if (w i).1 = (w i).2 then !(s i) else s i

theorem dualMask_injective {I : Type*} (w : Word I) : Function.Injective (dualMask w) := by
  apply Function.Involutive.injective
  intro s
  funext i
  by_cases h : (w i).1 = (w i).2 <;> simp [dualMask, h]

private def inputSlope {I : Type*} (w : Word I) (i : I) (s : Bool) : ℚ :=
  if s then
    if (w i).1 = (w i).2 then (w i).1 + 1 else (w i).2
  else (w i).1

private theorem inputSlope_ne {I : Type*} (w : Word I) (i : I) (s : Bool) :
    inputSlope w i s ≠ inputSlope w i (!s) := by
  by_cases h : (w i).1 = (w i).2
  · cases s <;> simp [inputSlope, h]
  · cases s <;> simp [inputSlope, h, Ne.symm h]

private def inputFactor {I : Type*} (w : Word I) (i : I) (s x : Bool) : ℚ :=
  if x then inputSlope w i s else 1

private def outputFactor {I : Type*} (w : Word I) (i : I) (R : Mask I) (x : Bool) : ℚ :=
  let s := dualMask w R i
  let other := inputSlope w i (!s)
  (if x then 1 else -other) / (inputSlope w i s - other)

private def maskRoots {I : Type*} [Fintype I] (a : I → ℚ) (s : Mask I) : ℚ[X] :=
  ∏ i ∈ ones s, (1 - C (a i)⁻¹ * X)

private theorem maskRoots_degree {I : Type*} [Fintype I] (a : I → ℚ) (s : Mask I) :
    (maskRoots a s).natDegree ≤ weight s := by
  apply (natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ _i ∈ ones s, 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (natDegree_sub_le ..).trans
      exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))
    _ = weight s := by simp [weight]

private theorem maskRoots_eval_zero {I : Type*} [Fintype I] (a : I → ℚ) (s : Mask I) :
    (maskRoots a s).eval 0 = 1 := by
  simp [maskRoots, eval_prod]

private theorem maskRoots_eval_node {I : Type*} [Fintype I] (a : I → ℚ) (s : Mask I) (t : I)
    (ha : a t ≠ 0) (hs : s t = true) : (maskRoots a s).eval (a t) = 0 := by
  rw [maskRoots, eval_prod]
  have ht : t ∈ ones s := by simp [ones, hs]
  exact Finset.prod_eq_zero ht (by simp [ha])

/-- Input mode in the common mask coordinates, with a root at each high slot. -/
def inputMode {I : Type*} [Fintype I] (a : I → ℚ) (w : Word I) (s x : Mask I) : ℚ[X] :=
  C (∏ i, inputFactor w i (s i) (x i)) * maskRoots a s

/-- Covector test for output word `w`, with a root at each high slot. -/
def outputTest {I : Type*} [Fintype I] (a : I → ℚ) (w : Word I) (R x : Mask I) : ℚ[X] :=
  C (∏ i, outputFactor w i R (x i)) * maskRoots a R

theorem inputMode_degree {I : Type*} [Fintype I] (a : I → ℚ) (w : Word I) (s x : Mask I) :
    (inputMode a w s x).natDegree ≤ weight s :=
  (natDegree_C_mul_le ..).trans (maskRoots_degree a s)

theorem outputTest_degree {I : Type*} [Fintype I] (a : I → ℚ) (w : Word I) (R x : Mask I) :
    (outputTest a w R x).natDegree ≤ weight R :=
  (natDegree_C_mul_le ..).trans (maskRoots_degree a R)

private theorem slot_pair {I : Type*} (w v : Word I) (i : I) (R : Mask I) (s : Bool) :
    (∑ b : Bool, outputFactor w i R b * inputFactor v i s b) =
      (inputSlope v i s - inputSlope w i (!(dualMask w R i))) /
        (inputSlope w i (dualMask w R i) - inputSlope w i (!(dualMask w R i))) := by
  simp [Fintype.univ_bool, outputFactor, inputFactor, div_eq_mul_inv]
  ring

private theorem slot_pair_same {I : Type*} (w : Word I) (i : I) (R : Mask I) (s : Bool) :
    (∑ b : Bool, outputFactor w i R b * inputFactor w i s b) =
      if s = dualMask w R i then 1 else 0 := by
  rw [slot_pair]
  by_cases h : s = dualMask w R i
  · rw [if_pos h, h, div_self (sub_ne_zero.mpr (inputSlope_ne w i _))]
  · have hs : s = !(dualMask w R i) := by
      cases s <;> cases e : dualMask w R i <;> simp_all
    rw [if_neg h, hs, sub_self, zero_div]

private theorem dualMask_twice {I : Type*} (w : Word I) (s : Mask I) :
    dualMask w (dualMask w s) = s := by
  funext i
  by_cases h : (w i).1 = (w i).2 <;> simp [dualMask, h]

private theorem mode_pair_eval {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℚ) (w v : Word I)
    (R s : Mask I) (z : ℚ) :
    (∑ x, (outputTest a w R x).eval z * (inputMode a v s x).eval z) =
      (∏ i, ∑ b : Bool, outputFactor w i R b * inputFactor v i (s i) b) *
        ((maskRoots a R).eval z * (maskRoots a s).eval z) := by
  classical
  simp only [outputTest, inputMode, eval_mul, eval_C]
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_mul_mul_comm, Finset.prod_mul_distrib]

/-- The normalized test selects the coefficient of its dual input mode at zero. -/
theorem outputTest_dot_inputMode_zero {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℚ) (w : Word I)
    (R s : Mask I) :
    (∑ x, (outputTest a w R x).eval 0 * (inputMode a w s x).eval 0) =
      if R = dualMask w s then 1 else 0 := by
  rw [mode_pair_eval]
  simp only [maskRoots_eval_zero, mul_one, slot_pair_same]
  by_cases h : R = dualMask w s
  · simp [h, dualMask_twice]
  · have hs : s ≠ dualMask w R := by
      intro e
      apply h
      rw [e, dualMask_twice]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ dualMask w R i := by
      by_contra! e
      exact hs (funext e)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- At a node, the test annihilates every input mode on an allowed physical pair. -/
theorem outputTest_half_pair {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℚ) (w v : Word I)
    (R s : Mask I) (t : I) (ha : a t ≠ 0) (hallowed : (v t).1 = (w t).2) :
    ∑ x, (outputTest a w R x).eval (a t) * (inputMode a v s x).eval (a t) = 0 := by
  rw [mode_pair_eval]
  by_cases hR : R t = true
  · rw [maskRoots_eval_node a R t ha hR, zero_mul, mul_zero]
  by_cases hs : s t = true
  · rw [maskRoots_eval_node a s t ha hs, mul_zero, mul_zero]
  have hRfalse : R t = false := Bool.eq_false_of_not_eq_true hR
  have hsfalse : s t = false := Bool.eq_false_of_not_eq_true hs
  have hother : inputSlope w t (!(dualMask w R t)) = (w t).2 := by
    by_cases hw : (w t).1 = (w t).2 <;> simp [dualMask, inputSlope, hRfalse, hw]
  have hslot : (∑ b : Bool, outputFactor w t R b * inputFactor v t (s t) b) = 0 := by
    rw [slot_pair, hother]
    simp [inputSlope, hsfalse, hallowed]
  rw [Finset.prod_eq_zero (Finset.mem_univ t) hslot, zero_mul]

/-- Coordinates of a tensor after fixing the slot `t` to its first coordinate. -/
abbrev Half {I : Type*} (t : I) := {i : I // i ≠ t} → Bool

def extendZero {I : Type*} [DecidableEq I] (t : I) (x : Half t) : Mask I :=
  fun i => if h : i = t then false else x ⟨i, h⟩

def lowFactor (c : ℚ) (b : Bool) : ℚ := if b then c else 1

theorem card_half {I : Type*} [Fintype I] [DecidableEq I] (t : I) :
    Fintype.card (Half t) = 2 ^ (Fintype.card I - 1) := by
  have h := Fintype.card_subtype_compl (fun i : I => i = t)
  have hc : Fintype.card {i : I // i = t} = 1 :=
    Fintype.card_unique
  change Fintype.card {i : I // i ≠ t} = Fintype.card I - Fintype.card {i : I // i = t} at h
  simp only [Half, Fintype.card_fun, Fintype.card_bool, h, hc]

theorem eval_inputMode_split {I : Type*} [Fintype I] [DecidableEq I]
    (nodes : I → ℚ) (w : Word I) (s x : Mask I) (t : I) (hn : nodes t ≠ 0) :
    (inputMode nodes w s x).eval (nodes t) =
      lowFactor (w t).1 (x t) *
        (inputMode nodes w s (extendZero t (fun i => x i.val))).eval (nodes t) := by
  simp only [inputMode, eval_mul, eval_C]
  by_cases hs : s t = true
  · simp [maskRoots_eval_node nodes s t hn hs]
  have hf : s t = false := Bool.eq_false_of_not_eq_true hs
  rw [← mul_assoc]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ (fun i => inputFactor w i (s i) (x i))
      (Finset.mem_univ t),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => inputFactor w i (s i) (extendZero t (fun i => x i.val) i))
      (Finset.mem_univ t)]
  have hp :
      (∏ i ∈ Finset.univ.erase t, inputFactor w i (s i) (x i)) =
      ∏ i ∈ Finset.univ.erase t, inputFactor w i (s i) (extendZero t (fun i => x i.val) i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [extendZero, (Finset.mem_erase.mp hi).1]
  rw [hp]
  simp [inputFactor, inputSlope, lowFactor, hf, extendZero]

end
end Reconstruction.LayoutMismatch
