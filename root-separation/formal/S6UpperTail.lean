import S6Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp

namespace Section6

open Finset
open scoped BigOperators

noncomputable section

def binMass (Q : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (Q.choose j : ℝ) * p ^ j * (1-p) ^ (Q-j)

lemma binMass_nonneg (Q j : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binMass Q p j := by unfold binMass; exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hp _)) (pow_nonneg (sub_nonneg.mpr hp1) _)

lemma bernoulli_exp_le (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    p * Real.exp (t * (1-p)) + (1-p) * Real.exp (-t*p) ≤ Real.exp (t^2) := by
  have h₁ : |t * (1-p)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-p)]
    nlinarith only [mul_le_mul_of_nonneg_right ht (show 0 ≤ 1-p by linarith), hp]
  have h₂ : |-t*p| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hp]
    nlinarith only [mul_le_mul_of_nonneg_right ht hp, hp1]
  have h₃ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h₁)).2
  have h₄ := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le h₂)).2
  have hle₁ : Real.exp (t * (1-p)) ≤ 1 + t * (1-p) + (t * (1-p))^2 := by
    linarith only [h₃]
  have hle₂ : Real.exp (-t*p) ≤ 1 + -t*p + (-t*p)^2 := by
    linarith only [h₄]
  calc
    _ ≤ p*(1+t*(1-p)+(t*(1-p))^2) + (1-p)*(1 + -t*p+(-t*p)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left hle₁ hp)
        (mul_le_mul_of_nonneg_left hle₂ (sub_nonneg.mpr hp1))
    _ = 1 + (p*(1-p))*t^2 := by ring
    _ ≤ 1 + t^2 := by
      have hh : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
      nlinarith only [mul_le_mul_of_nonneg_right hh (sq_nonneg t)]
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (t^2)

lemma bin_centered_mgf (Q : ℕ) (p t : ℝ) :
    ∑ j ∈ range (Q+1), Real.exp (t*((j : ℝ)-Q*p)) * binMass Q p j =
      (p * Real.exp (t*(1-p)) + (1-p) * Real.exp (-t*p)) ^ Q := by
  rw [add_pow]
  apply sum_congr rfl
  intro j hj
  have hjQ : j ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp hj)
  unfold binMass
  simp only [mul_pow, ← Real.exp_nat_mul, mul_assoc]
  have he : Real.exp (t*((j : ℝ)-Q*p)) =
      Real.exp ((j : ℝ)*(t*(1-p))) * Real.exp (((Q-j : ℕ) : ℝ)*(-t*p)) := by
    rw [← Real.exp_add, Nat.cast_sub hjQ]
    congr 1
    ring
  rw [he]
  ring

lemma bin_mgf_upper (Q : ℕ) (p t : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : |t| ≤ 1) :
    ∑ j ∈ range (Q+1), Real.exp (t*((j : ℝ)-Q*p)) * binMass Q p j ≤
      Real.exp ((Q : ℝ) * t^2) := by
  rw [bin_centered_mgf, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (add_nonneg (mul_nonneg hp (Real.exp_nonneg _)) (mul_nonneg (sub_nonneg.mpr hp1) (Real.exp_nonneg _))) (bernoulli_exp_le p t hp hp1 ht) _

/-- A two-sided upper tail sufficient for the source's tuned parameters, using
the elementary exponential series bound on the centered increments. -/
theorem bin_window_upper (Q : ℕ) (p s : ℝ) (window : Finset ℕ)
    (hQ : 0 < Q) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s) (hsQ : s ≤ 2*Q)
    (hw : ∀ j ∈ range (Q+1), j ∉ window → s ≤ |(j : ℝ)-Q*p|) :
    ∑ j ∈ (range (Q+1)).filter (· ∉ window), binMass Q p j ≤
      2 * Real.exp (-(s^2/(4*Q))) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  let t := s / (2*Q)
  have ht0 : 0 ≤ t := by unfold t; positivity
  have ht : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact (div_le_one (by positivity)).mpr hsQ
  let f (j : ℕ) := (Real.exp (t*((j : ℝ)-Q*p)) + Real.exp (-t*((j : ℝ)-Q*p))) *
    binMass Q p j
  have hf (j : ℕ) (hj : j ∈ (range (Q+1)).filter (· ∉ window)) :
      Real.exp (t*s) * binMass Q p j ≤ f j := by
    apply mul_le_mul_of_nonneg_right _ (binMass_nonneg Q j hp hp1)
    have hc := mul_le_mul_of_nonneg_left (hw j (mem_filter.mp hj).1 (mem_filter.mp hj).2) ht0
    apply (Real.exp_le_exp.mpr hc).trans
    by_cases hsign : 0 ≤ (j : ℝ)-Q*p
    · rw [abs_of_nonneg hsign]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hsign), mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have h := (sum_le_sum hf).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun j _ _ =>
      mul_nonneg (by positivity) (binMass_nonneg Q j hp hp1)))
  rw [← mul_sum] at h
  have hb : ∑ j ∈ range (Q+1), f j ≤ 2 * Real.exp ((Q : ℝ)*t^2) := by
    unfold f
    simp only [add_mul, sum_add_distrib]
    have h1 := bin_mgf_upper Q p t hp hp1 ht
    have h2 := bin_mgf_upper Q p (-t) hp hp1 (by simpa using ht)
    rw [neg_sq] at h2
    linarith only [h1, h2]
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (t*s))).mp
  calc
    _ ≤ 2 * Real.exp ((Q : ℝ)*t^2) := by
      have hh := h.trans hb
      linarith only [hh]
    _ = _ := by
      rw [mul_left_comm (Real.exp (t*s)), ← Real.exp_add]
      congr 2
      unfold t
      field_simp
      ring

#print axioms bin_centered_mgf
#print axioms bin_window_upper

end
end Section6


