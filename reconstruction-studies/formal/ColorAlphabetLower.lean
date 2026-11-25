import ReceiverOrderOptimal
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.GeomSum

open scoped BigOperators Polynomial

namespace Reconstruction.ColorAlphabet

noncomputable section

/-- The finite Woolsey–Chen–Ji receiver-order count in homogeneous alphabets. -/
def uniformConverse (q r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range r, rate (j+1) * (((j+1 : ℕ) : ℚ)^(2*q) - (j : ℚ)^(2*q))

theorem uniform_potential (q r : ℕ) :
    orderPotential (fun _ : Fin q => r) r = uniformConverse q r := by
  rw [potential_sum, uniformConverse]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j+1 ≤ r := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  simp only [clippedVolume, min_eq_right hj', min_eq_right (Nat.le_of_succ_le hj'),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-- The sum over first-demand positions, with the alphabet index shifted down
by one. The term at zero vanishes, giving the double sum in equation (1). -/
theorem uniform_converse_double_sum (q r : ℕ) :
    uniformConverse q r = ∑ j ∈ Finset.range r, ∑ t ∈ Finset.range q,
      (j : ℚ)^(2*t+1) * (((j+1 : ℕ) : ℚ)^(2*(q-1-t))) := by
  rw [uniformConverse]
  apply Finset.sum_congr rfl
  intro j _
  let x : ℚ := ((j : ℚ)+1)^2
  let y : ℚ := (j : ℚ)^2
  have hj : 0 ≤ (j : ℚ) := Nat.cast_nonneg _
  have hxy : x ≠ y := by dsimp [x, y]; intro h; nlinarith
  have hg := (Commute.all y x).geom_sum₂ hxy.symm q
  have hquot : (y^q-x^q)/(y-x) = (x^q-y^q)/(x-y) := by
    rw [← neg_sub (x^q) (y^q), ← neg_sub x y, neg_div_neg_eq]
  have hden : x-y = 2*((j : ℚ)+1)-1 := by dsimp [x, y]; ring
  calc
    _ = (j : ℚ) * ((x^q-y^q)/(x-y)) := by
      rw [rate, hden]
      simp only [x, y, Nat.cast_add, Nat.cast_one, ← pow_mul]
      field_simp (disch := linarith) <;> ring
    _ = (j : ℚ) * ∑ t ∈ Finset.range q, y^t * x^(q-1-t) := by rw [hg, hquot]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [x, y, ← pow_mul, pow_add, pow_one, Nat.cast_add, Nat.cast_one]
      ring

private theorem rate_increment (j : ℕ) (hj : 0 < j) :
    rate (j+1) - rate j = 1 / (4*(j : ℚ)^2-1) := by
  have hj' : 1 ≤ (j : ℚ) := by exact_mod_cast hj
  have h1 : (2*(j : ℚ)-1) ≠ 0 := by linarith
  have h2 : (2*((j : ℚ)+1)-1) ≠ 0 := by linarith
  have h3 : (4*(j : ℚ)^2-1) ≠ 0 := by nlinarith
  unfold rate
  push_cast
  field_simp (disch := nlinarith) <;> ring

theorem uniform_converse_telescoped (q r : ℕ) (hr : 0 < r) :
    uniformConverse q r =
      rate r * (r : ℚ)^(2*q) -
        ∑ j ∈ Finset.range (r-1), ((j+1 : ℕ) : ℚ)^(2*q) / (4*((j+1 : ℕ) : ℚ)^2-1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  clear hr
  induction r with
  | zero =>
    simp [uniformConverse, rate]
  | succ r ih =>
    have he : r+1-1 = r := by omega
    have he' : r+1+1-1 = r+1 := by omega
    rw [he] at ih
    rw [he', uniformConverse, Finset.sum_range_succ, ← uniformConverse, ih, Finset.sum_range_succ]
    have hg := rate_increment (r+1) (by omega)
    have hf := congrArg (((r+1 : ℕ) : ℚ)^(2*q) * ·) hg
    dsimp only at hf
    rw [mul_sub, div_eq_mul_inv, one_mul] at hf
    simp only [div_eq_mul_inv]
    linarith only [hf]

/-- The uniform receiver-order converse for every recovery matrix over every field. -/
theorem uniform_rank_lower {F I : Type*} [Field F] [Fintype I] (q r : ℕ)
    (C : Matrix I (Word (fun _ : Fin q => Fin r)) F) (hC : Recovers C) :
    uniformConverse q r ≤ (C.rank : ℚ) := by
  obtain ⟨S, hS, h⟩ :=
    (receiver_order_maximum (A := fun _ : Fin q => Fin r) r (by simp)).2.1
  simp only [Fintype.card_fin] at h
  rw [← uniform_potential q r, h]
  exact_mod_cast generalizedIndependent_rank_le C hC S hS

theorem uniform_rank_lower_polynomial {F I : Type*} [Field F] [Fintype I] (q r : ℕ)
    (a : Fin q → F) (C : Matrix I (Word (fun _ : Fin q => Fin r)) F)
    (P : Matrix (Word (fun _ : Fin q => Fin r)) (Word (fun _ : Fin q => Fin r)) F[X])
    (h : FeasibleZero a C P) :
    uniformConverse q r ≤ (C.rank : ℚ) :=
  uniform_rank_lower q r C (feasibleZero_recovers h)

theorem binary_converse_value (q : ℕ) :
    uniformConverse q 2 = ((4^q : ℚ)-1)/3 := by
  rw [uniformConverse]
  norm_num [Finset.sum_range_succ, rate, pow_mul] <;> ring

theorem binary_field_rank_lower {F I : Type*} [Field F] [Fintype I] (q : ℕ)
    (C : Matrix I (Word (fun _ : Fin q => Fin 2)) F) (hC : Recovers C) :
    (4^q-1)/3 ≤ C.rank := by
  have h := uniform_rank_lower q 2 C hC
  rw [binary_converse_value] at h
  have hn : 1 ≤ 4^q := Nat.one_le_pow _ _ (by decide)
  have h₁ : ((((4^q-1)/3 : ℕ) * 3 : ℕ) : ℚ) ≤ (4^q : ℚ)-1 := by
    exact_mod_cast (Nat.div_mul_le_self (4^q-1) 3)
  have h₂ : ((((4^q-1)/3 : ℕ) : ℚ)) ≤ (C.rank : ℚ) := by
    push_cast at h₁
    linarith
  exact_mod_cast h₂

end

end Reconstruction.ColorAlphabet
