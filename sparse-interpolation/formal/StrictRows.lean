import StrictLocal
import MatrixRows
import Alternants

open scoped BigOperators fwdDiff
open Polynomial SharpDifference

namespace GrenetStrict

variable (p : ℕ) [Fact p.Prime]

/-- The series (exp(c W) - 1) / c, defined without division in the local ring. -/
noncomputable def kernel (c : ℚ) (hc : StrictStep p c) : PowerSeries (D p) :=
  PowerSeries.X ^ 1 * PowerSeries.mk (kernelCoeff p c hc)

theorem kernel_reduce (c : ℚ) (hc : StrictStep p c) :
    PowerSeries.map (residue p) (kernel p c hc) = PowerSeries.X := by
  rw [kernel, map_mul, map_pow, PowerSeries.map_X, pow_one]
  have he : PowerSeries.map (residue p) (PowerSeries.mk (kernelCoeff p c hc)) = 1 := by
    apply PowerSeries.ext
    intro r
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_one, reduce_kernelCoeff]
  rw [he, mul_one]

noncomputable def kernelQ (c : ℚ) (hc : StrictStep p c) : PowerSeries ℚ :=
  PowerSeries.map (toRat p) (kernel p c hc)

theorem exp_sub_one (c : ℚ) (hc : StrictStep p c) :
    PowerSeries.rescale c (PowerSeries.exp ℚ) - 1 =
      PowerSeries.C c * kernelQ p c hc := by
  apply PowerSeries.ext
  intro r
  rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, kernelQ, PowerSeries.coeff_map, kernel,
    PowerSeries.coeff_X_pow_mul']
  cases r with
  | zero => norm_num
  | succ r =>
    rw [if_neg (Nat.succ_ne_zero r), sub_zero, if_pos (show 1 ≤ r+1 by omega),
      Nat.add_sub_cancel, PowerSeries.coeff_mk, toRat_kernelCoeff, kernelRat]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, pow_succ, div_eq_mul_inv, one_mul]
    ring

/-- The finite row polynomial over the p-local coefficient ring. -/
noncomputable def rowPoly (c : ℚ) (hc : StrictStep p c) (M i : ℕ) : Polynomial (D p) :=
  ∑ r ∈ Finset.range (M+1),
    Polynomial.C (PowerSeries.coeff r ((kernel p c hc)^i)) * descPochhammer (D p) r

theorem rowPoly_reduce (c : ℚ) (hc : StrictStep p c) (M i : ℕ) (hi : i ≤ M) :
    (rowPoly p c hc M i).map (residue p) =
      descPochhammer (IsLocalRing.ResidueField (D p)) i := by
  have hcoeff (r : ℕ) : residue p (PowerSeries.coeff r (kernel p c hc ^ i)) =
      if r = i then 1 else 0 := by
    rw [← PowerSeries.coeff_map, map_pow, kernel_reduce, PowerSeries.coeff_X_pow]
  unfold rowPoly
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    descPochhammer_map, hcoeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro r _ hr
    simp [hr]
  · simp [Finset.mem_range, Nat.lt_succ_of_le hi]

theorem fwdDiff_row (c : ℚ) (hc : StrictStep p c) (M e i : ℕ) (he : e ≤ M) :
    (Δ_[1]^[i] (fun j : ℕ => (1 + (j : ℚ) * c)^e)) 0 =
      c^i * toRat p ((rowPoly p c hc M i).eval (e : D p)) := by
  rw [fwdDiff_binomial c M e i he, exp_sub_one p c hc, mul_pow, ← map_pow]
  unfold rowPoly
  change _ = c^i * (toRat p) (Polynomial.evalRingHom (e : D p) _)
  simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial, map_natCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [PowerSeries.coeff_C_mul, kernelQ, ← map_pow, PowerSeries.coeff_map]
  ring

end GrenetStrict

