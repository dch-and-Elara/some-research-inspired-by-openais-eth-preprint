import LocalTwo
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown

open scoped BigOperators fwdDiff

namespace SharpDifference

abbrev UPoly := Polynomial ℚ
abbrev LocalPoly := Polynomial D

noncomputable def liftPoly : LocalPoly →+* UPoly := Polynomial.mapRingHom toRat

noncomputable def twoU : UPoly := 2 * Polynomial.X

/-- The series with coefficient 2^(r-1) U^(r-1) / r! at each positive r. -/
noncomputable def kernel : PowerSeries LocalPoly :=
  PowerSeries.X ^ 1 * PowerSeries.mk (fun r => Polynomial.monomial r (scaledFactorial r))

@[simp] theorem coeff_kernel_zero : PowerSeries.coeff 0 kernel = 0 := by
  simp [kernel]

@[simp] theorem coeff_kernel_succ (r : ℕ) :
    PowerSeries.coeff (r + 1) kernel = Polynomial.monomial r (scaledFactorial r) := by
  rw [kernel, PowerSeries.coeff_X_pow_mul', if_pos (show 1 ≤ r + 1 by omega),
    Nat.add_sub_cancel, PowerSeries.coeff_mk]

theorem coeff_kernel_pow_zero_of_lt {r i : ℕ} (h : r < i) :
    PowerSeries.coeff r (kernel ^ i) = 0 := by
  rw [kernel, mul_pow, ← pow_mul, one_mul, PowerSeries.coeff_X_pow_mul',
    if_neg (Nat.not_le_of_lt h)]

/-- A common truncation through M suffices for every output coefficient through M,
even after taking arbitrary powers. -/
theorem coeff_pow_common_truncation {A : Type*} [CommSemiring A]
    (H : PowerSeries A) (M i r : ℕ) (h : r ≤ M) :
    Polynomial.coeff ((PowerSeries.trunc (M + 1) H) ^ i) r = PowerSeries.coeff r (H ^ i) := by
  have hr : r < M + 1 := Nat.lt_succ_of_le h
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow,
    ← PowerSeries.coeff_coe_trunc_of_lt hr, PowerSeries.trunc_trunc_pow,
    PowerSeries.coeff_coe_trunc_of_lt hr]

/-- The coefficient polynomial in the exponent T over the actual local coefficient ring. -/
noncomputable def rowPoly (M i : ℕ) : Polynomial LocalPoly :=
  ∑ r ∈ Finset.Icc i M,
    Polynomial.C (PowerSeries.coeff r (kernel ^ i)) * descPochhammer LocalPoly r

theorem rowPoly_finite (M i : ℕ) :
    rowPoly M i = ∑ r ∈ Finset.Icc i M,
      Polynomial.C (Polynomial.coeff ((PowerSeries.trunc (M + 1) kernel) ^ i) r) *
        descPochhammer LocalPoly r := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [coeff_pow_common_truncation _ _ _ _ (Finset.mem_Icc.mp hr).2]

theorem rowPoly_eq_sum_range (M i : ℕ) :
    rowPoly M i = ∑ r ∈ Finset.range (M + 1),
      Polynomial.C (PowerSeries.coeff r (kernel ^ i)) * descPochhammer LocalPoly r := by
  unfold rowPoly
  apply Finset.sum_subset
  · intro r hr
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hr).2)
  · intro r hr hn
    have h : r < i := by
      have hm := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      by_contra! hh
      exact hn (Finset.mem_Icc.mpr ⟨hh, hm⟩)
    simp [coeff_kernel_pow_zero_of_lt h]

section ExpCurve

variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def expCurve (c : A) (j : ℕ) : PowerSeries A :=
  PowerSeries.rescale ((j : A) * c) (PowerSeries.exp A)

theorem expCurve_succ (c : A) (j : ℕ) :
    expCurve c (j + 1) = expCurve c j * PowerSeries.rescale c (PowerSeries.exp A) := by
  rw [expCurve, expCurve, PowerSeries.exp_mul_exp_eq_exp_add]
  congr 1
  push_cast
  ring

theorem expCurve_zero (c : A) : expCurve c 0 = 1 := by
  simp [expCurve]

/-- Forward differentiation is exact on the entire formal exponential sequence. -/
theorem fwdDiff_expCurve (c : A) (i j : ℕ) :
    (Δ_[1]^[i] (expCurve c)) j =
      (PowerSeries.rescale c (PowerSeries.exp A) - 1) ^ i * expCurve c j := by
  induction i generalizing j with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih, ih, expCurve_succ, pow_succ]
    ring

theorem map_fwdDiff {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (g : X →+ Y) (f : ℕ → X) (i j : ℕ) :
    g ((Δ_[1]^[i] f) j) = (Δ_[1]^[i] (g ∘ f)) j := by
  induction i generalizing j with
  | zero => rfl
  | succ i ih =>
    simp only [Function.iterate_succ_apply', fwdDiff, map_sub, ih]

theorem choose_mul_pow_eq_expCoeff (c : A) (e r j : ℕ) :
    (e.choose r : A) * ((j : A) * c) ^ r =
      (e.descFactorial r : A) * PowerSeries.coeff r (expCurve c j) := by
  rw [expCurve, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hfac : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hm : (r.factorial : A) * algebraMap ℚ A (1 / (r.factorial : ℚ)) = 1 := by
    rw [← map_natCast (algebraMap ℚ A), ← map_mul, mul_one_div_cancel hfac, map_one]
  calc
    _ = ((e.choose r : A) * ((j : A) * c) ^ r) *
        ((r.factorial : A) * algebraMap ℚ A (1 / (r.factorial : ℚ))) := by rw [hm, mul_one]
    _ = _ := by ring

theorem binomial_eq_expCoeff_sum (c : A) (M e j : ℕ) (he : e ≤ M) :
    (1 + (j : A) * c) ^ e =
      ∑ r ∈ Finset.range (M + 1), (e.descFactorial r : A) *
        PowerSeries.coeff r (expCurve c j) := by
  calc
    _ = ∑ r ∈ Finset.range (e + 1), (e.choose r : A) * ((j : A) * c) ^ r := by
      rw [add_comm, add_pow]
      simp [mul_comm]
    _ = ∑ r ∈ Finset.range (M + 1), (e.choose r : A) * ((j : A) * c) ^ r := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ he))
      intro r _ hr
      have hlt : e < r := by simpa [Finset.mem_range] using hr
      simp [Nat.choose_eq_zero_of_lt hlt]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact choose_mul_pow_eq_expCoeff c e r j

/-- The finite binomial expansion can be differenced coefficientwise with the same M. -/
theorem fwdDiff_binomial (c : A) (M e i : ℕ) (he : e ≤ M) :
    (Δ_[1]^[i] (fun j : ℕ => (1 + (j : A) * c) ^ e)) 0 =
      ∑ r ∈ Finset.range (M + 1), (e.descFactorial r : A) *
        PowerSeries.coeff r ((PowerSeries.rescale c (PowerSeries.exp A) - 1) ^ i) := by
  have hfun : (fun j : ℕ => (1 + (j : A) * c) ^ e) =
      ∑ r ∈ Finset.range (M + 1), (e.descFactorial r : A) •
        (fun j : ℕ => PowerSeries.coeff r (expCurve c j)) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
      binomial_eq_expCoeff_sum c M e j he
  rw [hfun, fwdDiff_iter_finset_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (Δ_[1]^[i] ((PowerSeries.coeff r).toAddMonoidHom ∘ expCurve c)) 0 = _
  rw [← map_fwdDiff]
  simp [fwdDiff_expCurve, expCurve_zero]

end ExpCurve

noncomputable def kernelQ : PowerSeries UPoly := PowerSeries.map liftPoly kernel

theorem coeff_kernelQ_pow (i r : ℕ) :
    PowerSeries.coeff r (kernelQ ^ i) = liftPoly (PowerSeries.coeff r (kernel ^ i)) := by
  rw [kernelQ, ← map_pow, PowerSeries.coeff_map]

theorem exp_sub_one_eq_C_mul_kernelQ :
    PowerSeries.rescale twoU (PowerSeries.exp UPoly) - 1 =
      PowerSeries.C twoU * kernelQ := by
  apply PowerSeries.ext
  intro r
  cases r with
  | zero =>
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul, kernelQ, PowerSeries.coeff_map, coeff_kernel_zero]
    norm_num
  | succ r =>
    rw [map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero r), sub_zero, PowerSeries.coeff_C_mul, kernelQ,
      PowerSeries.coeff_map, coeff_kernel_succ]
    change _ = twoU * (Polynomial.monomial r (scaledFactorial r)).map toRat
    rw [Polynomial.map_monomial, toRat_scaledFactorial, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hc : (2 : UPoly) ^ r * Polynomial.C (1 / ((r + 1).factorial : ℚ)) =
        Polynomial.C ((2 : ℚ) ^ r / ((r + 1).factorial : ℚ)) := by
      have ht : Polynomial.C (2 : ℚ) = (2 : UPoly) :=
        Polynomial.C_eq_natCast (R := ℚ) 2
      calc
        _ = Polynomial.C (2 : ℚ) ^ r * Polynomial.C (1 / ((r + 1).factorial : ℚ)) := by
          rw [ht]
        _ = _ := by
          rw [← Polynomial.C_pow, ← Polynomial.C_mul]
          simp [div_eq_mul_inv]
    rw [← hc, pow_succ]
    have hu : twoU ^ r = (2 : UPoly) ^ r * Polynomial.X ^ r := by
      simp [twoU, mul_pow]
    rw [hu]
    ring

theorem liftPoly_eval_rowPoly (M i e : ℕ) :
    liftPoly ((rowPoly M i).eval (e : LocalPoly)) =
      ∑ r ∈ Finset.range (M + 1), (e.descFactorial r : UPoly) *
        PowerSeries.coeff r (kernelQ ^ i) := by
  rw [rowPoly_eq_sum_range]
  change liftPoly ((Polynomial.evalRingHom (e : LocalPoly)) _) = _
  simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial, map_natCast, coeff_kernelQ_pow]
  apply Finset.sum_congr rfl
  intro r _
  exact mul_comm _ _

/-- Denominator-free row normalization, valid even at U = 0 after specialization. -/
theorem fwdDiff_rowPoly (M e i : ℕ) (he : e ≤ M) :
    (Δ_[1]^[i] (fun j : ℕ => (1 + (j : UPoly) * twoU) ^ e)) 0 =
      twoU ^ i * liftPoly ((rowPoly M i).eval (e : LocalPoly)) := by
  rw [fwdDiff_binomial twoU M e i he, exp_sub_one_eq_C_mul_kernelQ, mul_pow, ← map_pow,
    liftPoly_eval_rowPoly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [PowerSeries.coeff_C_mul]
  ring

theorem eval_rowPoly_common_truncation {M N e i : ℕ} (hM : e ≤ M) (hN : e ≤ N) :
    liftPoly ((rowPoly M i).eval (e : LocalPoly)) =
      liftPoly ((rowPoly N i).eval (e : LocalPoly)) := by
  have h2u : twoU ≠ 0 := mul_ne_zero (by norm_num) Polynomial.X_ne_zero
  exact mul_left_cancel₀ (pow_ne_zero i h2u)
    ((fwdDiff_rowPoly M e i hM).symm.trans (fwdDiff_rowPoly N e i hN))


noncomputable def atZero : LocalPoly →+* D := Polynomial.evalRingHom 0

theorem kernel_map_atZero : PowerSeries.map atZero kernel = PowerSeries.X := by
  rw [kernel, map_mul, map_pow, PowerSeries.map_X, pow_one]
  have h : PowerSeries.map atZero
      (PowerSeries.mk (fun r => Polynomial.monomial r (scaledFactorial r))) = 1 := by
    apply PowerSeries.ext
    intro r
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    change (Polynomial.monomial r (scaledFactorial r)).eval 0 = _
    rw [Polynomial.eval_monomial]
    cases r with
    | zero =>
      simp only [pow_zero, mul_one]
      apply Subtype.ext
      change (2 : ℚ) ^ 0 / ((0 + 1).factorial : ℚ) = 1
      norm_num
    | succ r =>
      simp
  rw [h, mul_one]

theorem rowPoly_atZero (M i : ℕ) (hi : i ≤ M) :
    (rowPoly M i).map atZero = descPochhammer D i := by
  have hc (r : ℕ) :
      atZero (PowerSeries.coeff r (kernel ^ i)) = if r = i then 1 else 0 := by
    rw [← PowerSeries.coeff_map, map_pow, kernel_map_atZero, PowerSeries.coeff_X_pow]
  unfold rowPoly
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, descPochhammer_map, hc]
  rw [Finset.sum_eq_single i]
  · simp
  · intro r _ hr
    simp [hr]
  · simp [Finset.mem_Icc, hi]

end SharpDifference


