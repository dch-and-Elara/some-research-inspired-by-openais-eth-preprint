import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring

open scoped BigOperators Polynomial
open Polynomial

namespace Reconstruction.ReleaseColor.Walsh

noncomputable section

variable {I : Type*} [DecidableEq I]

private def nodalBasis (nodes : Finset ℕ) (j : ℕ) : ℚ[X] :=
  ∏ i ∈ nodes.erase j, C (((j : ℚ) - (i : ℚ))⁻¹) * (X - C (i : ℚ))

/-- Interpolate the alternating signs on the integer retained interval. -/
def signs (L U : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.Icc L U, C ((-1 : ℚ)^j) * nodalBasis (Finset.Icc L U) j

private theorem nodalBasis_eval_self (nodes : Finset ℕ) (j : ℕ) :
    (nodalBasis nodes j).eval (j : ℚ) = 1 := by
  rw [nodalBasis, eval_prod]
  apply Finset.prod_eq_one
  intro i hi
  have hji : (j : ℚ) ≠ (i : ℚ) := by exact_mod_cast (Finset.mem_erase.mp hi).1.symm
  simp [inv_mul_cancel₀ (sub_ne_zero.mpr hji)]

private theorem nodalBasis_eval_other {nodes : Finset ℕ} {j k : ℕ}
    (hk : k ∈ nodes) (hne : k ≠ j) : (nodalBasis nodes j).eval (k : ℚ) = 0 := by
  rw [nodalBasis, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hk⟩) (by simp)

private theorem signs_eval {L U j : ℕ} (hj : j ∈ Finset.Icc L U) :
    (signs L U).eval (j : ℚ) = (-1 : ℚ)^j := by
  simp only [signs, eval_finset_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single j]
  · rw [nodalBasis_eval_self, mul_one]
  · intro i _ hij
    rw [nodalBasis_eval_other hj hij.symm, mul_zero]
  · exact fun h => False.elim (h hj)

private theorem signs_degree (L U : ℕ) : (signs L U).natDegree ≤ U-L := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le ..).trans
  unfold nodalBasis
  apply (natDegree_prod_le ..).trans
  calc
    _ ≤ ∑ _i ∈ (Finset.Icc L U).erase j, 1 := by
      apply Finset.sum_le_sum
      intro i _
      exact (natDegree_C_mul_le ..).trans (natDegree_X_sub_C_le _)
    _ = U-L := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj, Nat.card_Icc]
      simp
      omega

private def siteFactor (a : I → ℚ) (i : I) : ℚ[X] := 1 - C (a i)⁻¹ * X

def totalAt (a : I → ℚ) (S : Finset I) : ℚ[X] := ∑ i ∈ S, siteFactor a i

private theorem totalAt_zero (a : I → ℚ) (S : Finset I) :
    (totalAt a S).eval 0 = (S.card : ℚ) := by
  simp [totalAt, siteFactor, eval_finset_sum]

private theorem totalAt_degree (a : I → ℚ) (S : Finset I) :
    (totalAt a S).natDegree ≤ 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  unfold siteFactor
  apply (natDegree_sub_le ..).trans
  exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))

/-- Toggle the slot of a Walsh index. -/
def toggle (t : I) (S : Finset I) : Finset I :=
  if t ∈ S then S.erase t else insert t S

private theorem toggle_twice (t : I) (S : Finset I) :
    toggle t (toggle t S) = S := by
  by_cases h : t ∈ S
  · simp [toggle, h, Finset.insert_erase h]
  · simp [toggle, h]

private def toggleEquiv (t : I) : Finset I ≃ Finset I :=
  ⟨toggle t, toggle t, toggle_twice t, toggle_twice t⟩

private theorem totalAt_toggle_node (a : I → ℚ) (t : I) (h : a t ≠ 0) (S : Finset I) :
    (totalAt a (toggle t S)).eval (a t) = (totalAt a S).eval (a t) := by
  have ht : (siteFactor a t).eval (a t) = 0 := by simp [siteFactor, h, inv_mul_cancel₀ h]
  by_cases hS : t ∈ S
  · have he := congrArg (eval (a t)) (Finset.sum_erase_add S (siteFactor a) hS)
    simpa [toggle, hS, totalAt, ht] using he
  · simp [toggle, hS, totalAt, Finset.sum_insert, ht]

private theorem toggle_weight_sign (t : I) (S : Finset I) :
    (-1 : ℚ)^(toggle t S).card = -((-1 : ℚ)^S.card) := by
  by_cases h : t ∈ S
  · have he := Finset.card_erase_add_one h
    rw [toggle, if_pos h, ← he, pow_succ]
    ring
  · rw [toggle, if_neg h, Finset.card_insert_of_notMem h, pow_succ]
    ring

/-- The exact retained-interval multiplier from the manuscript. -/
def multiplier (a : I → ℚ) (L U : ℕ) (S : Finset I) : ℚ[X] :=
  if S.card ∈ Finset.Icc L U then C ((-1 : ℚ)^S.card) * (signs L U).comp (totalAt a S)
  else 1

theorem multiplier_degree (a : I → ℚ) (L U : ℕ) (S : Finset I) :
    (multiplier a L U S).natDegree ≤ U-L := by
  by_cases h : S.card ∈ Finset.Icc L U
  · rw [multiplier, if_pos h]
    exact (natDegree_C_mul_le ..).trans <| natDegree_comp_le.trans <|
      (Nat.mul_le_mul (signs_degree L U) (totalAt_degree a S)).trans (by simp)
  · simp [multiplier, h]

theorem multiplier_zero (a : I → ℚ) (L U : ℕ) (S : Finset I) :
    (multiplier a L U S).eval 0 = 1 := by
  by_cases h : S.card ∈ Finset.Icc L U
  · rw [multiplier, if_pos h, eval_mul, eval_C, eval_comp, totalAt_zero, signs_eval h,
      ← mul_pow]
    simp
  · simp [multiplier, h]

theorem multiplier_toggle (a : I → ℚ) (L U : ℕ) (t : I) (ht : a t ≠ 0) (S : Finset I)
    (hS : S.card ∈ Finset.Icc L U) (hT : (toggle t S).card ∈ Finset.Icc L U) :
    (multiplier a L U (toggle t S)).eval (a t) = -(multiplier a L U S).eval (a t) := by
  simp only [multiplier, hS, hT, if_true, eval_mul, eval_C, eval_comp]
  rw [totalAt_toggle_node a t ht, toggle_weight_sign, neg_mul]


variable [Fintype I]

private def phase (b : Bool) : ℚ := if b then -1 else 1

private theorem phase_sq (b : Bool) : phase b * phase b = 1 := by cases b <;> norm_num [phase]

private theorem phase_ne_pair {b c : Bool} (h : b ≠ c) : phase b * phase c = -1 := by
  cases b <;> cases c <;> simp_all [phase]

private theorem phase_ne_zero (b : Bool) : phase b ≠ 0 := by cases b <;> norm_num [phase]

def character (S : Finset I) (u : I → Bool) : ℚ := ∏ i ∈ S, phase (u i)

private theorem character_toggle (t : I) (S : Finset I) (u : I → Bool) :
    character (toggle t S) u = phase (u t) * character S u := by
  by_cases h : t ∈ S
  · have he := Finset.mul_prod_erase S (fun i => phase (u i)) h
    rw [toggle, if_pos h, character, character, ← he, ← mul_assoc, phase_sq, one_mul]
  · simp [toggle, h, character, Finset.prod_insert]

private theorem sum_toggle_zero (t : I) (f : Finset I → ℚ)
    (h : ∀ S, f (toggle t S) = -f S) : (∑ S, f S) = 0 := by
  have he := (toggleEquiv t).sum_comp f
  change (∑ S, f (toggle t S)) = ∑ S, f S at he
  simp_rw [h, Finset.sum_neg_distrib] at he
  linarith

private theorem character_pair (u v : I → Bool) :
    (∑ S : Finset I, character S u * character S v) =
      if u = v then (2 : ℚ)^Fintype.card I else 0 := by
  by_cases h : u = v
  · subst v
    have hS (S : Finset I) : character S u * character S u = 1 := by
      rw [character, ← Finset.prod_mul_distrib]
      simp [phase_sq]
    simp [hS, Fintype.card_finset]
  · obtain ⟨t, ht⟩ : ∃ t, u t ≠ v t := by
      by_contra! he
      exact h (funext he)
    rw [if_neg h]
    apply sum_toggle_zero t
    intro S
    dsimp only
    rw [character_toggle, character_toggle, mul_mul_mul_comm, phase_ne_pair ht, neg_one_mul]

def coefficient (S : Finset I) (z : (I → Bool) → ℚ) : ℚ :=
  ∑ v, z v * character S v

private theorem coefficient_toggle (z : (I → Bool) → ℚ) (t : I) (u : I → Bool)
    (hz : ∀ v, v t ≠ u t → z v = 0) (S : Finset I) :
    coefficient (toggle t S) z = phase (u t) * coefficient S z := by
  unfold coefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [character_toggle]
  by_cases h : v t = u t
  · rw [h, mul_left_comm]
  · rw [hz v h, zero_mul, zero_mul, mul_zero]

/-- The exact Walsh-diagonal polynomial matrix stated in the orbit proof. -/
def walshMatrix (a : I → ℚ) (L U : ℕ) (u v : I → Bool) : ℚ[X] :=
  C (((2 : ℚ)^Fintype.card I)⁻¹) *
    ∑ S : Finset I, C (character S u * character S v) * multiplier a L U S

theorem walshMatrix_degree (a : I → ℚ) (L U : ℕ) (u v : I → Bool) :
    (walshMatrix a L U u v).natDegree ≤ U-L := by
  unfold walshMatrix
  refine (natDegree_C_mul_le ..).trans (natDegree_sum_le_of_forall_le _ _ ?_)
  intro S _
  exact (natDegree_C_mul_le ..).trans (multiplier_degree a L U S)

theorem walshMatrix_zero (a : I → ℚ) (L U : ℕ) (u v : I → Bool) :
    (walshMatrix a L U u v).eval 0 = if u = v then 1 else 0 := by
  simp only [walshMatrix, eval_mul, eval_C, eval_finset_sum, multiplier_zero, mul_one]
  rw [character_pair]
  by_cases h : u = v
  · rw [if_pos h, if_pos h, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))]
  · simp [h]

/-- Kernel inputs supported on the output's unknown orientation are annihilated
at that node. The measured Walsh modes are precisely the complement of the band. -/
theorem walshMatrix_local (a : I → ℚ) (L U : ℕ) (u : I → Bool) (t : I) (ht : a t ≠ 0)
    (z : (I → Bool) → ℚ) (hz : ∀ v, v t ≠ u t → z v = 0)
    (hk : ∀ S, S.card ∉ Finset.Icc L U → coefficient S z = 0) :
    ∑ v, (walshMatrix a L U u v).eval (a t) * z v = 0 := by
  let f (S : Finset I) : ℚ := character S u * coefficient S z * (multiplier a L U S).eval (a t)
  have hzero : (∑ S, f S) = 0 := by
    apply sum_toggle_zero t
    intro S
    have hcoeff := coefficient_toggle z t u hz S
    have hchar := character_toggle t S u
    by_cases hS : S.card ∈ Finset.Icc L U
    · by_cases hT : (toggle t S).card ∈ Finset.Icc L U
      · change character (toggle t S) u * coefficient (toggle t S) z *
            (multiplier a L U (toggle t S)).eval (a t) =
          -(character S u * coefficient S z * (multiplier a L U S).eval (a t))
        rw [hcoeff, hchar, multiplier_toggle a L U t ht S hS hT, mul_mul_mul_comm,
          phase_sq, one_mul, mul_neg]
      · have he := hk (toggle t S) hT
        have hc : coefficient S z = 0 := by
          rw [hcoeff] at he
          exact (mul_eq_zero.mp he).resolve_left (phase_ne_zero _)
        simp [f, he, hc]
    · have he := hk S hS
      simp [f, he, hcoeff]
  simp only [walshMatrix, eval_mul, eval_C, eval_finset_sum, mul_assoc]
  rw [← Finset.mul_sum]
  apply mul_eq_zero_of_right
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, ← hzero]
  apply Finset.sum_congr rfl
  intro S _
  dsimp only [f]
  rw [coefficient, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  ring


/-- The diagonal gate of the manuscript on an orbit with few active sites. -/
def diagonalGate (a : I → ℚ) (active : Finset I) : ℚ[X] :=
  ∏ t ∈ active, siteFactor a t

theorem diagonalGate_properties (a : I → ℚ) (active : Finset I)
    (hn : ∀ t ∈ active, a t ≠ 0) :
    (diagonalGate a active).natDegree ≤ active.card ∧
      (diagonalGate a active).eval 0 = 1 ∧
      ∀ t ∈ active, (diagonalGate a active).eval (a t) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply (natDegree_prod_le ..).trans
    calc
      _ ≤ ∑ _t ∈ active, 1 := by
        apply Finset.sum_le_sum
        intro t _
        unfold siteFactor
        apply (natDegree_sub_le ..).trans
        exact max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp))
      _ = _ := by simp
  · simp [diagonalGate, siteFactor, eval_prod]
  · intro t ht
    rw [diagonalGate, eval_prod]
    exact Finset.prod_eq_zero ht (by simp [siteFactor, hn t ht])

end
end Reconstruction.ReleaseColor.Walsh
