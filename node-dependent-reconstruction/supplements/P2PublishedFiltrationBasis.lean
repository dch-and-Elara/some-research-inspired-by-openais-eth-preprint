import LayoutMismatchPacking
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Paper 2, Section 4: the actual tensor coordinates of the published
input modes and the monic interpolation factors used in its filtration. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I : Type*} [Fintype I]

/-- The manuscript's monic factor `π_S`. -/
def rootProduct (nodes : I → ℚ) (s : Mask I) : ℚ[X] :=
  ∏ t ∈ ones s, (X - C (nodes t))

theorem rootProduct_monic (nodes : I → ℚ) (s : Mask I) :
    (rootProduct nodes s).Monic := by
  unfold rootProduct
  exact monic_prod_of_monic (ones s) _ (fun _ _ => monic_X_sub_C _)

theorem rootProduct_degree (nodes : I → ℚ) (s : Mask I) :
    (rootProduct nodes s).natDegree = weight s := by
  unfold rootProduct weight
  rw [natDegree_prod _ _ (fun _ _ => X_sub_C_ne_zero _)]
  simp

theorem rootProduct_atZero_ne (nodes : I → ℚ) (s : Mask I)
    (hne : ∀ t, nodes t ≠ 0) : (rootProduct nodes s).eval 0 ≠ 0 := by
  unfold rootProduct
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  simpa using hne t

theorem rootProduct_at_node (nodes : I → ℚ) (s : Mask I) (t : I) (ht : s t = true) :
    (rootProduct nodes s).eval (nodes t) = 0 := by
  unfold rootProduct
  rw [eval_prod]
  have hm : t ∈ ones s := by simp [ones, ht]
  exact Finset.prod_eq_zero hm (by simp)

/-- A degree-zero normalized published mode gives the constant tensor basis
coordinate. It does not depend on the actual interpolation nodes. -/
def basisEntry (w : Word I) (s x : Mask I) : ℚ :=
  (inputMode (fun _ => 0) w s x).eval 0

def normalizedRootProduct (nodes : I → ℚ) (s : Mask I) : ℚ[X] :=
  ∏ t ∈ ones s, (1 - C (nodes t)⁻¹ * X)

theorem normalized_root_product_eval_zero (nodes : I → ℚ) (s : Mask I) :
    (normalizedRootProduct nodes s).eval 0 = 1 := by
  simp [normalizedRootProduct, eval_prod]

theorem input_mode_is_basis_times_normalized_roots
    (nodes : I → ℚ) (w : Word I) (s x : Mask I) :
    inputMode nodes w s x = C (basisEntry w s x) * normalizedRootProduct nodes s := by
  unfold basisEntry inputMode
  change C _ * normalizedRootProduct nodes s =
    C ((C _ * normalizedRootProduct (fun _ => 0) s).eval 0) * normalizedRootProduct nodes s
  rw [eval_mul, eval_C, normalized_root_product_eval_zero, mul_one]

theorem mode_at_zero_is_basis (nodes : I → ℚ) (w : Word I) (s x : Mask I) :
    (inputMode nodes w s x).eval 0 = basisEntry w s x := by
  rw [input_mode_is_basis_times_normalized_roots, eval_mul, eval_C,
    normalized_root_product_eval_zero, mul_one]

variable [DecidableEq I]

/-- For a low factor at t, the physical tensor is determined by its actual
t-false half coordinates and the shared two-vector (1, source slope). -/
theorem basis_entry_half_split (w : Word I) (s x : Mask I) (t : I) (hs : s t = false) :
    basisEntry w s x = lowFactor (w t).1 (x t) *
      basisEntry w s (extendZero t (fun i => x i.val)) := by
  let trial : I → ℚ := fun i => if i = t then 1 else 0
  have ht : trial t ≠ 0 := by simp [trial]
  have hp : normalizedRootProduct trial s = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have h : i ≠ t := by
      rintro rfl
      simp [ones, hs] at hi
    simp [trial, h]
  have h := eval_inputMode_split trial w s x t ht
  simpa only [input_mode_is_basis_times_normalized_roots, hp, mul_one, eval_C] using h

def basisSynthesis (w : Word I) : (Mask I → ℚ) →ₗ[ℚ] (Mask I → ℚ) where
  toFun c x := ∑ s, c s * basisEntry w s x
  map_add' c d := by
    funext x
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext x
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem published_basis_dual (w : Word I) (s b : Mask I) :
    (∑ x, (outputTest (fun _ => 0) w (dualMask w s) x).eval 0 * basisEntry w b x) =
      if s = b then 1 else 0 := by
  unfold basisEntry
  rw [outputTest_dot_inputMode_zero]
  simp only [(dualMask_injective w).eq_iff]

theorem published_basis_is_injective (w : Word I) : Function.Injective (basisSynthesis w) := by
  classical
  have recover (c : Mask I → ℚ) (s : Mask I) :
      (∑ x, (outputTest (fun _ => 0) w (dualMask w s) x).eval 0 * basisSynthesis w c x) =
        c s := by
    change (∑ x, (outputTest (fun _ => 0) w (dualMask w s) x).eval 0 *
      ∑ b, c b * basisEntry w b x) = c s
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_left_comm _ (c _) _, ← Finset.mul_sum, published_basis_dual]
    simp
  intro c d eq
  funext s
  rw [← recover c s, ← recover d s, eq]

/-- Not merely independent modes: the actual scalar tensor coordinates
are equivalent to the full M-dimensional physical tensor space. -/
def publishedBasisEquiv (w : Word I) : (Mask I → ℚ) ≃ₗ[ℚ] (Mask I → ℚ) :=
  LinearEquiv.ofInjectiveEndo (basisSynthesis w) (published_basis_is_injective w)

#print axioms rootProduct_monic
#print axioms rootProduct_degree
#print axioms rootProduct_atZero_ne
#print axioms rootProduct_at_node
#print axioms input_mode_is_basis_times_normalized_roots
#print axioms basis_entry_half_split
#print axioms published_basis_dual
#print axioms publishedBasisEquiv
end
end Reconstruction.LayoutMismatch.PublishedFiltration

