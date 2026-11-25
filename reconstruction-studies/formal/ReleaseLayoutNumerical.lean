import VisitRuntime
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
Exact numerical steps displayed in the first v2 PDF. The runtime modules
already prove the two asymptotic bounds with estimates sufficient for their
conclusions. These lemmas record the paper's displayed constants and logs.
-/

namespace Reconstruction.VisitRuntime

open scoped BigOperators

/-- The precise logarithmic schedule cap on page 7. -/
theorem paper_schedule_cap {n r A : ℝ} {Q : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hloglog : 0 < Real.log (Real.log n))
    (hgroup : Real.log (Real.log n) / 3 ≤ Real.log r)
    (hschedule : r^(2*Q) ≤ n^A) :
    (Q : ℝ) ≤ (3*A/2) * Real.log n / Real.log (Real.log n) := by
  have h := Real.log_le_log (pow_pos hr _) hschedule
  rw [Real.log_pow, Real.log_rpow hn] at h
  push_cast at h
  apply (le_div_iff₀ hloglog).mpr
  have hq := (mul_le_mul_of_nonneg_left hgroup (by positivity : 0 ≤ 2*(Q:ℝ))).trans h
  linarith only [hq]

/-- The binomial lower bound used in the Taylor-subset branch. -/
theorem paper_pow_div_le_choose {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    ((n:ℝ)/(s:ℝ))^s ≤ (n.choose s:ℝ) := by
  have hprod :
      (∏ i ∈ Finset.range s, ((n-i : ℕ) : ℝ) / ((s-i : ℕ) : ℝ)) = (n.choose s:ℝ) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_self, Nat.cast_mul]
    exact mul_div_cancel_left₀ _ (by positivity)
  rw [← hprod, ← Finset.card_range s, ← Finset.prod_const]
  simp only [Finset.card_range]
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hsi : i ≤ s := hi'.le
  have hni : i ≤ n := hsi.trans hsn
  rw [Nat.cast_sub hsi, Nat.cast_sub hni]
  apply (div_le_div_iff₀ (by exact_mod_cast hs) (sub_pos.mpr (by exact_mod_cast hi'))).mpr
  have hs' : (s:ℝ) ≤ n := by exact_mod_cast hsn
  nlinarith only [mul_nonneg (show (0:ℝ) ≤ i by positivity) (sub_nonneg.mpr hs')]

/-- The exact displayed Taylor logarithm, with natural logarithms. -/
theorem paper_log_choose {n s : ℕ} (hs : 0 < s) (hsn : s ≤ n) :
    (s:ℝ) * Real.log ((n:ℝ)/(s:ℝ)) ≤ Real.log (n.choose s : ℝ) := by
  have hn := hs.trans_le hsn
  have hpos : 0 < ((n:ℝ)/(s:ℝ))^s :=
    pow_pos (div_pos (by exact_mod_cast hn) (by exact_mod_cast hs)) _
  simpa only [Real.log_pow] using Real.log_le_log hpos (paper_pow_div_le_choose hs hsn)

/-- The paper's (\sqrt{\log(e q)/q}) is decreasing on ([1,\infty)). -/
theorem paper_node_rate_antitone :
    AntitoneOn (fun q : ℝ => Real.sqrt (Real.log (Real.exp 1 * q) / q)) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hquot : 1 ≤ y/x := (le_div_iff₀ hx0).mpr (by simpa using hxy)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at h
  have hscaled : 1 + Real.log y ≤ (y/x)*(1 + Real.log x) := calc
    _ ≤ y/x + Real.log x := by linarith only [h]
    _ ≤ _ := by
      rw [mul_add, mul_one]
      exact add_le_add_left (le_mul_of_one_le_left hlogx hquot) _
  apply Real.sqrt_le_sqrt
  rw [Real.log_mul (Real.exp_ne_zero _) hy0.ne', Real.log_mul (Real.exp_ne_zero _) hx0.ne',
    Real.log_exp]
  apply (div_le_div_iff₀ hy0 hx0).mpr
  have hh := mul_le_mul_of_nonneg_right hscaled hx0.le
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hx0.ne'] at hh
  simpa only [mul_comm y (1 + Real.log x)] using hh

/-- The exact binary-entropy margin used for the sixteen-permutation union bound. -/
theorem paper_entropy_margin :
    (1/4:ℝ) < 7/8 -
      (-(1/8 * Real.log (1/8) + 7/8 * Real.log (7/8))/Real.log 2) := by
  have hlog2 := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have hp := Real.log_lt_log (show (0:ℝ) < 2^19 by positivity)
    (show (2:ℝ)^19 < 7^7 by norm_num)
  rw [Real.log_pow, Real.log_pow] at hp
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num), hlog8]
  have haux : (-(1/8 * (Real.log 1 - 3 * Real.log 2) +
      7/8 * (Real.log 7 - 3 * Real.log 2)))/Real.log 2 < 5/8 := by
    apply (div_lt_iff₀ hlog2).mpr
    norm_num only [Nat.cast_ofNat, Real.log_one] at hp ⊢
    linarith only [hp]
  linarith only [haux]

/-- Counting operations with a fixed positive charge per record changes a
natural-log lower bound by the corresponding additive constant. -/
theorem paper_log_cost_conversion {charge visits operations lower : ℝ}
    (hcharge : 0 < charge) (hvisits : 0 < visits) (hwork : charge * visits ≤ operations)
    (hlower : lower ≤ Real.log visits) :
    Real.log charge + lower ≤ Real.log operations := by
  calc
    _ ≤ Real.log charge + Real.log visits := add_le_add_left hlower _
    _ = Real.log (charge * visits) := (Real.log_mul hcharge.ne' hvisits.ne').symm
    _ ≤ _ := Real.log_le_log (mul_pos hcharge hvisits) hwork

end Reconstruction.VisitRuntime
