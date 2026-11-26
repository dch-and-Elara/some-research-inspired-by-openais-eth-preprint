/-
Analytic adapters based on Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
(Eric Wieser and Yaël Dillies, Apache 2.0). The pinned deployment has those
sources but not that module's object; put the tiny cosh argument in a
distinct namespace to preserve both clean replay and normal Mathlib builds.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace Paper5.FrontendG1.Tanner
open NormedSpace
open scoped Nat

theorem expSeries_cosh_complex (z : ℂ) :
    HasSum (fun n : ℕ => z^(2*n)/↑(2*n)!) (Complex.cosh z) := by
  rw [Complex.cosh,Complex.exp_eq_exp_ℂ]
  have h := ((expSeries_div_hasSum_exp ℂ z).add
    (expSeries_div_hasSum_exp ℂ (-z))).div_const 2
  replace h := (Nat.divModEquiv 2).symm.hasSum_iff.mpr h
  dsimp [Function.comp_def] at h
  simp_rw [←mul_comm 2 _] at h
  refine h.prod_fiberwise fun k=>?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2→ℂ) using 1
  rw [Fin.sum_univ_two]
  simp_rw [Fin.val_zero,Fin.val_one,add_zero,pow_succ,pow_mul,neg_sq,←two_mul,
    mul_neg,neg_div,add_neg_cancel,zero_div,add_zero,
    mul_div_cancel_left₀ _ (two_ne_zero : (2:ℂ)≠0)]

theorem expSeries_cosh_real (x : ℝ) :
    HasSum (fun n : ℕ => x^(2*n)/↑(2*n)!) (Real.cosh x) :=
  mod_cast expSeries_cosh_complex x

theorem cosh_exponential_bound (x : ℝ) : Real.cosh x≤Real.exp (x^2/2) := by
  rw [(expSeries_cosh_real x).tsum_eq.symm,Real.exp_eq_exp_ℝ,exp_eq_tsum]
  refine (expSeries_cosh_real x).summable.tsum_le_tsum (fun i=>?_) <|
    expSeries_summable' (x^2/2)
  simp only [div_pow,pow_mul,smul_eq_mul,inv_mul_eq_div,div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul _

#print axioms expSeries_cosh_complex
#print axioms expSeries_cosh_real
#print axioms cosh_exponential_bound
end Paper5.FrontendG1.Tanner