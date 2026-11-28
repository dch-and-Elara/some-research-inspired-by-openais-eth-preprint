import BooleanCube.MatrixCertificates
import Mathlib.Algebra.Polynomial.RingDivision

/-! Paper 1 §7: the literal divisibility-defined input test space, and its
identification with the original public zero-half evaluations. -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The original input-coordinate polynomial `Q_v`. -/
def literalInputProduct {q : ℕ} (a : Fin q → ℚ) (v : Cube q) : ℚ[X] :=
  ∏ i ∈ ones v, (1 - C (a i)⁻¹ * X)

theorem literal_input_product_zero {q : ℕ} (a : Fin q → ℚ) (v : Cube q) :
    (literalInputProduct a v).eval 0 = 1 := by
  simp [literalInputProduct, eval_prod]

private theorem normalized_factor_eq (a : ℚ) (ha : a ≠ 0) :
    1 - C a⁻¹ * X = C (-a⁻¹) * (X-C a) := by
  rw [mul_sub, ← map_mul, neg_mul, inv_mul_cancel₀ ha]
  simp only [map_neg, map_one]
  ring

/-- Exact equivalence of the paper's normalized product divisibility and
vanishing at its recorded labels. Distinctness and nonzeroness are explicit. -/
theorem literal_input_product_dvd_iff {q : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) (v : Cube q) (p : ℚ[X]) :
    literalInputProduct a v ∣ p ↔ ∀ i ∈ ones v, p.eval (a i) = 0 := by
  have units : IsUnit (∏ i ∈ ones v, C (-(a i)⁻¹) : ℚ[X]) :=
    IsUnit.prod_iff.mpr fun i _ => isUnit_C.mpr (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero (hn i))))
  unfold literalInputProduct
  simp_rw [normalized_factor_eq _ (hn _)]
  rw [Finset.prod_mul_distrib, units.mul_left_dvd]
  constructor
  · intro h i hi
    exact dvd_iff_isRoot.mp ((Finset.dvd_prod_of_mem (fun j => X - C (a j)) hi).trans h)
  · intro h
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun he => hij (ha he))))
    · intro i hi
      exact dvd_iff_isRoot.mpr (h i hi)

theorem literal_input_divisibility_iff_zero_half {q : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) (h : Cube q → ℚ[X]) :
    (∀ v, literalInputProduct a v ∣ h v) ↔ zeroHalfTests a h := by
  simp_rw [literal_input_product_dvd_iff ha hn]
  constructor
  · intro he i x hx
    exact he x i (by simp [ones,hx])
  · intro he x i hi
    exact he i x (by simpa [ones] using hi)

/-- Each factor is the bounded polynomials divisible by its own `Q_v`.
We use the isomorphic evaluation-kernel carrier to give it a module structure. -/
abbrev literalInputTestSpace {q : ℕ} (a : Fin q → ℚ) (j : ℕ) :=
  (v : Cube q) → LinearMap.ker (rootSamples (n := j+1) a v)

theorem literal_input_test_space_membership {q j : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) (h : Cube q → Bounded (j+1)) :
    (∀ v, h v ∈ LinearMap.ker (rootSamples a v)) ↔
      ∀ v, literalInputProduct a v ∣ (h v).val := by
  simp_rw [literal_input_product_dvd_iff ha hn]
  constructor
  · intro he v i hi
    exact congrFun (LinearMap.mem_ker.mp (he v)) (⟨i,hi⟩ : ↥(ones v))
  · intro he v
    apply LinearMap.mem_ker.mpr
    funext i
    exact he v i i.property

/-- The dimension calculation `dim H_j = N_q(j)` for the actual input
space of Section 7, not the different edge-equality spline space. -/
theorem literal_input_test_space_dimension {q : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (j : ℕ) :
    Module.finrank ℚ (literalInputTestSpace a j) =
      ∑ k ∈ Finset.range (q+1), (j+1-k)*q.choose k := by
  classical
  letI (s : Cube q) : Module.Free ℚ (LinearMap.ker (rootSamples (n := j+1) a s)) := by
    apply @Module.Free.of_divisionRing ℚ ↥(LinearMap.ker (rootSamples (n := j+1) a s)) _ _ _
  letI (s : Cube q) : Module.Finite ℚ (LinearMap.ker (rootSamples (n := j+1) a s)) :=
    inferInstance
  unfold literalInputTestSpace
  rw [Module.finrank_pi_fintype ℚ]
  simp_rw [root_kernel_dim ha]
  have hw (s : Cube q) (_ : s ∈ Finset.univ) : weight s ∈ Finset.range (q+1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (by simpa [weight] using (ones s).card_le_univ)
  rw [← Finset.sum_fiberwise_of_maps_to hw]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ _s ∈ (Finset.univ.filter fun s : Cube q => weight s = k), (j+1-k) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    _ = _ := by simp [layer_size, Nat.mul_comm]

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.literal_input_product_zero
#print axioms LocalReconstruction.Paper1Coverage.literal_input_product_dvd_iff
#print axioms LocalReconstruction.Paper1Coverage.literal_input_divisibility_iff_zero_half
#print axioms LocalReconstruction.Paper1Coverage.literal_input_test_space_membership
#print axioms LocalReconstruction.Paper1Coverage.literal_input_test_space_dimension
