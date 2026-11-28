import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace LocalReconstruction

abbrev Cube (q : ℕ) := Fin q → Bool

def signBit : Bool → Bool → ℚ
  | true, true => -1
  | _, _ => 1

def walsh {q : ℕ} (s x : Cube q) : ℚ :=
  ∏ i, signBit (s i) (x i)

theorem walsh_comm {q : ℕ} (s x : Cube q) : walsh s x = walsh x s := by
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> cases x i <;> rfl

private theorem local_sum (a b : Bool) :
    (∑ x : Bool, signBit a x * signBit b x) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [Fintype.univ_bool, signBit]

theorem walsh_orthogonal {q : ℕ} (s t : Cube q) :
    (∑ x : Cube q, walsh s x * walsh t x) = if s = t then (2 : ℚ)^q else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => signBit (s i) b * signBit (t i) b)]
  simp only [local_sum]
  split_ifs with h
  · subst t
    simp
  · obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := by
      by_contra! a
      exact h (funext a)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem synthesis {q : ℕ} (f : Cube q → ℚ) (x : Cube q) :
    (∑ s : Cube q, (∑ y : Cube q, f y * walsh s y) * walsh s x) = 2^q * f x := by
  classical
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have h (y : Cube q) :
      (∑ s : Cube q, walsh s y * walsh s x) = if y = x then (2 : ℚ)^q else 0 := by
    calc
      _ = ∑ s : Cube q, walsh y s * walsh x s := by
        apply Finset.sum_congr rfl
        intro s _
        rw [walsh_comm s y, walsh_comm s x]
      _ = _ := walsh_orthogonal y x
  simp_rw [h, mul_ite, mul_zero]
  simp [mul_comm]

theorem walsh_independent (q : ℕ) : LinearIndependent ℚ (@walsh q) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have hz (x : Cube q) : (∑ y : Cube q, c y * walsh y x) = 0 := by
    simpa [Finset.sum_apply] using congrFun hc x
  have z (x : Cube q) : (∑ y : Cube q, c y * walsh x y) = 0 := by
    calc
      _ = ∑ y : Cube q, c y * walsh y x := by
        apply Finset.sum_congr rfl
        intro y _
        rw [walsh_comm x y]
      _ = 0 := hz x
  have h := synthesis c s
  simp only [z, zero_mul, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by norm_num))

noncomputable def walshBasis (q : ℕ) : Module.Basis (Cube q) ℚ (Cube q → ℚ) :=
  basisOfLinearIndependentOfCardEqFinrank (walsh_independent q)
    (Module.finrank_fintype_fun_eq_card ℚ).symm

@[simp] theorem walshBasis_apply (q : ℕ) (s : Cube q) :
    walshBasis q s = walsh s := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank (walsh_independent q)
    (Module.finrank_fintype_fun_eq_card ℚ).symm) s

end LocalReconstruction
