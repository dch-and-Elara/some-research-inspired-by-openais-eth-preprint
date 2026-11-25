import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Variance with a bounded dependency neighborhood

A finite rational law and a family of bounded variables suffice. The
off-neighborhood mixed terms vanish. Counting the remaining ordered pairs
bounds the second moment of a weighted sum, including negative coefficients.
-/

namespace LocalVariance

open scoped BigOperators

variable {Ω E : Type*} [Fintype Ω] [Fintype E]

def mean (μ z : Ω → ℚ) : ℚ := ∑ w, μ w * z w

def covariance (μ : Ω → ℚ) (Z : E → Ω → ℚ) (a : E → ℚ) (e f : E) : ℚ :=
  ∑ w, μ w * ((Z e w - a e) * (Z f w - a f))

/-- Exact expansion, before any probabilistic inequality. -/
theorem weighted_square_expansion (μ : Ω → ℚ) (Z : E → Ω → ℚ) (a d : E → ℚ) :
    (∑ w, μ w * ((∑ e, d e * Z e w) - ∑ e, d e * a e) ^ 2) =
      ∑ e, ∑ f, d e * d f * covariance μ Z a e f := by
  have hpoint (w : Ω) : μ w * ((∑ e, d e * Z e w) - ∑ e, d e * a e) ^ 2 =
      ∑ e, ∑ f, d e * d f * (μ w * ((Z e w - a e) * (Z f w - a f))) := by
    have hcenter : (∑ e, d e * Z e w) - ∑ e, d e * a e = ∑ e, d e * (Z e w - a e) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    simp only [hcenter, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  simp only [covariance, Finset.mul_sum]

/-- A probability-weighted mean of variables in the unit interval around
zero is again in that interval. -/
theorem abs_mean_le_one (μ z : Ω → ℚ) (hμ : ∀ w, 0 ≤ μ w) (hmass : ∑ w, μ w = 1)
    (hz : ∀ w, |z w| ≤ 1) : |mean μ z| ≤ 1 := by
  calc
    _ ≤ ∑ w, |μ w * z w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, μ w := by
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul, abs_of_nonneg (hμ w)]
      simpa using mul_le_mul_of_nonneg_left (hz w) (hμ w)
    _ = _ := hmass

omit [Fintype E] in
/-- A centered variable has absolute value at most two, so each covariance
has absolute value at most four. -/
theorem abs_covariance_le_four (μ : Ω → ℚ) (Z : E → Ω → ℚ) (a : E → ℚ)
    (hμ : ∀ w, 0 ≤ μ w) (hmass : ∑ w, μ w = 1)
    (hZ : ∀ e w, |Z e w| ≤ 1) (ha : ∀ e, |a e| ≤ 1) (e f : E) :
    |covariance μ Z a e f| ≤ 4 := by
  have hcenter (i : E) (w : Ω) : |Z i w - a i| ≤ 2 := by
    calc
      _ ≤ |Z i w| + |a i| := abs_sub _ _
      _ ≤ 2 := by linarith only [hZ i w, ha i]
  calc
    _ ≤ ∑ w, |μ w * ((Z e w - a e) * (Z f w - a f))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, μ w * 4 := by
      apply Finset.sum_le_sum
      intro w _
      rw [abs_mul, abs_of_nonneg (hμ w), abs_mul]
      apply mul_le_mul_of_nonneg_left _ (hμ w)
      exact (mul_le_mul (hcenter e w) (hcenter f w) (abs_nonneg _) (by decide)).trans_eq (by norm_num)
    _ = 4 := by rw [← Finset.sum_mul, hmass, one_mul]

/-- At most `C` ordered partners contribute in each row of the covariance
matrix. The constants `a` may be any valid centers with the stated vanishing
mixed moments. -/
theorem bounded_dependency_variance (μ : Ω → ℚ) (Z : E → Ω → ℚ) (a d : E → ℚ)
    (dep : E → Finset E) (C : ℕ)
    (hμ : ∀ w, 0 ≤ μ w) (hmass : ∑ w, μ w = 1)
    (hZ : ∀ e w, |Z e w| ≤ 1) (ha : ∀ e, |a e| ≤ 1) (hd : ∀ e, |d e| ≤ 1)
    (hcov : ∀ e f, f ∉ dep e → covariance μ Z a e f = 0)
    (hdeg : ∀ e, (dep e).card ≤ C) :
    (∑ w, μ w * ((∑ e, d e * Z e w) - ∑ e, d e * a e) ^ 2) ≤
      4 * (Fintype.card E : ℚ) * C := by
  classical
  have hpair (e f : E) : d e * d f * covariance μ Z a e f ≤ 4 := by
    calc
      _ ≤ |d e * d f * covariance μ Z a e f| := le_abs_self _
      _ = |d e| * |d f| * |covariance μ Z a e f| := by rw [abs_mul, abs_mul]
      _ ≤ (1 * 1) * 4 := mul_le_mul
        (mul_le_mul (hd e) (hd f) (abs_nonneg _) zero_le_one)
        (abs_covariance_le_four μ Z a hμ hmass hZ ha e f) (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hrow (e : E) : (∑ f, d e * d f * covariance μ Z a e f) ≤ 4 * C := by
    calc
      _ = ∑ f ∈ dep e, d e * d f * covariance μ Z a e f := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro f _ hf
        rw [hcov e f hf, mul_zero]
      _ ≤ ∑ _f ∈ dep e, (4 : ℚ) := Finset.sum_le_sum fun f _ => hpair e f
      _ = 4 * ((dep e).card : ℚ) := by simp [mul_comm]
      _ ≤ 4 * C := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hdeg e)) (by decide)
  rw [weighted_square_expansion]
  calc
    _ ≤ ∑ _e : E, 4 * (C : ℚ) := Finset.sum_le_sum fun e _ => hrow e
    _ = _ := by simp [mul_assoc, mul_left_comm]

omit [Fintype E] in
/-- Express the covariance through ordinary first and second product moments. -/
theorem covariance_means (μ : Ω → ℚ) (Z : E → Ω → ℚ) (hmass : ∑ w, μ w = 1) (e f : E) :
    covariance μ Z (fun i => mean μ (Z i)) e f =
      mean μ (fun w => Z e w * Z f w) - mean μ (Z e) * mean μ (Z f) := by
  let a := mean μ (Z e)
  let b := mean μ (Z f)
  have hpoint (w : Ω) : μ w * ((Z e w - a) * (Z f w - b)) =
      μ w * (Z e w * Z f w) - b * (μ w * Z e w) - a * (μ w * Z f w) + (a * b) * μ w := by
    ring
  change (∑ w, μ w * ((Z e w - a) * (Z f w - b))) = (∑ w, μ w * (Z e w * Z f w)) - a * b
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_one]
  change _ - b * a - a * b + a * b = _ - a * b
  ring

/-- The variance bound with actual means. Off-neighborhood independence only
needs to supply factorization of the ordinary pair moments. -/
theorem variance_of_factorization (μ : Ω → ℚ) (Z : E → Ω → ℚ) (d : E → ℚ)
    (dep : E → Finset E) (C : ℕ)
    (hμ : ∀ w, 0 ≤ μ w) (hmass : ∑ w, μ w = 1)
    (hZ : ∀ e w, |Z e w| ≤ 1) (hd : ∀ e, |d e| ≤ 1)
    (hpair : ∀ e f, f ∉ dep e →
      mean μ (fun w => Z e w * Z f w) = mean μ (Z e) * mean μ (Z f))
    (hdeg : ∀ e, (dep e).card ≤ C) :
    (∑ w, μ w * ((∑ e, d e * Z e w) - ∑ e, d e * mean μ (Z e)) ^ 2) ≤
      4 * (Fintype.card E : ℚ) * C := by
  apply bounded_dependency_variance μ Z _ d dep C hμ hmass hZ
    (fun e => abs_mean_le_one μ (Z e) hμ hmass (hZ e)) hd _ hdeg
  intro e f hef
  rw [covariance_means μ Z hmass, hpair e f hef, sub_self]

/-- Symmetric support blocks of at most `D` sites have at most `D²`
potentially interacting partners per variable. Outside that two-step union
the supports are disjoint. -/
theorem variance_of_disjoint_blocks (μ : Ω → ℚ) (Z : E → Ω → ℚ) (d : E → ℚ)
    (B : E → Finset E) (D : ℕ)
    (hμ : ∀ w, 0 ≤ μ w) (hmass : ∑ w, μ w = 1)
    (hZ : ∀ e w, |Z e w| ≤ 1) (hd : ∀ e, |d e| ≤ 1)
    (hsym : ∀ e f, f ∈ B e → e ∈ B f) (hsize : ∀ e, (B e).card ≤ D)
    (hindep : ∀ e f, Disjoint (B e) (B f) →
      mean μ (fun w => Z e w * Z f w) = mean μ (Z e) * mean μ (Z f)) :
    (∑ w, μ w * ((∑ e, d e * Z e w) - ∑ e, d e * mean μ (Z e)) ^ 2) ≤
      4 * (Fintype.card E : ℚ) * (D * D : ℕ) := by
  classical
  let dep (e : E) := (B e).biUnion B
  apply variance_of_factorization μ Z d dep (D * D) hμ hmass hZ hd
  · intro e f hfar
    apply hindep e f (Finset.disjoint_left.mpr ?_)
    intro k hke hkf
    exact hfar (Finset.mem_biUnion.mpr ⟨k, hke, hsym f k hkf⟩)
  · intro e
    exact (Finset.card_biUnion_le_card_mul (B e) B D (fun k _ => hsize k)).trans
      (Nat.mul_le_mul_right _ (hsize e))

#print axioms weighted_square_expansion
#print axioms abs_mean_le_one
#print axioms abs_covariance_le_four
#print axioms bounded_dependency_variance
#print axioms covariance_means
#print axioms variance_of_factorization
#print axioms variance_of_disjoint_blocks

end LocalVariance
