import P2PublishedFiltrationEq9

/-! The printed origin-coordinate vanishing step, on the literal
filtration kernel rather than a specially packed payload. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open LayoutBudget (GroupFiber)
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V G : Type*} [Fintype I] [DecidableEq I] [Fintype G]
variable (node : I → ℚ) (a b : I → V → G)

def tensorPolynomial (h : Polys V I) (v : V) (x : Mask I) : ℚ[X] :=
  ∑ s : Mask I, C (basisEntry (layoutWord a b v) s x) * h (v,s)

theorem tensor_polynomial_eval (h : Polys V I) (v : V) (x : Mask I) (z : ℚ) :
    (tensorPolynomial a b h v x).eval z = tensorAt a b h v x z := by
  simp only [tensorPolynomial,tensorAt,eval_finset_sum,eval_mul,eval_C]

theorem tensor_polynomial_degree (j : ℕ) {h : Polys V I} (hh : h ∈ H node j)
    (v : V) (x : Mask I) : (tensorPolynomial a b h v x).natDegree ≤ j := by
  unfold tensorPolynomial
  apply natDegree_sum_le_of_forall_le
  intro s _
  apply (natDegree_C_mul_le ..).trans
  have d := ((mem_Hlt node (j+1) h).1 hh v s).1
  by_cases z : h (v,s)=0
  · simp [z]
  rw [degree_eq_natDegree z,Nat.cast_lt] at d
  omega

theorem normalized_root_nonzero_on_low_coordinate (s : Mask I) (t : I)
    (injective : Function.Injective node) (nonzero : ∀ i, node i ≠ 0) (low : s t = false) :
    (normalizedRootProduct node s).eval (node t) ≠ 0 := by
  rw [normalizedRootProduct,eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have ne : i ≠ t := by
    rintro rfl
    simp [ones,low] at hi
  simp only [eval_sub,eval_one,eval_mul,eval_C,eval_X]
  intro zero
  have z : (node i)⁻¹ * node t = 1 := (sub_eq_zero.mp zero).symm
  have bad : node t = node i := by
    have e := congrArg (fun q : ℚ=>node i*q) z
    simpa [← mul_assoc,nonzero i] using e
  exact ne (injective bad.symm)

private theorem dot_tensor_sum (f c : Mask I → ℚ) (e : Mask I → Mask I → ℚ) :
    (∑ x, f x * ∑ s, e s x * c s) = ∑ s, (∑ x, f x * e s x)*c s := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun x _ => (mul_assoc _ _ _).symm))

theorem low_basis_orthogonal_at_allowed_site (s tmask : Mask I) (u v : V) (t : I)
    (inj : Function.Injective node) (nonzero : ∀ i, node i ≠ 0)
    (allowed : a t v=b t u) (low : s t=false) :
    ∑ x, (outputTest node (layoutWord a b u) tmask x).eval (node t) *
       basisEntry (layoutWord a b v) s x = 0 := by
  have ne := normalized_root_nonzero_on_low_coordinate node s t inj nonzero low
  apply (mul_eq_zero.mp ?_).resolve_right ne
  rw [Finset.sum_mul]
  simp_rw [mul_assoc]
  have h := outputTest_half_pair node (layoutWord a b u) (layoutWord a b v) tmask s t
    (nonzero t) (congrArg groupSlope allowed)
  simpa only [input_mode_is_basis_times_normalized_roots,eval_mul,eval_C] using h

variable [Fintype V]

theorem nodal_test_annihilates_allowed_tensor (j : ℕ) {h : Polys V I} (hh : h ∈ H node j)
    (B : Mask I) (u v : V) (t : I) (inj : Function.Injective node) (nonzero : ∀ i, node i ≠ 0)
    (allowed : a t v=b t u) :
    ∑ x, (outputTest node (layoutWord a b u) B x).eval (node t) *
      tensorAt a b h v x (node t) = 0 := by
  unfold tensorAt
  rw [dot_tensor_sum]
  apply Finset.sum_eq_zero
  intro s _
  by_cases high : s t=true
  · rw [high_coordinate_at_its_node_is_zero node (j+1) hh v s t high, mul_zero]
  rw [low_basis_orthogonal_at_allowed_site node a b s B u v t inj nonzero allowed
    (Bool.eq_false_of_not_eq_true high),zero_mul]

theorem output_test_origin_unchanged (w : Word I) (B x : Mask I) :
    (outputTest node w B x).eval 0 = (outputTest (fun _=>0) w B x).eval 0 := by
  unfold outputTest
  change (C _ * normalizedRootProduct node B).eval 0 =
    (C _ * normalizedRootProduct (fun _=>0) B).eval 0
  simp only [eval_mul,eval_C,normalized_root_product_eval_zero,mul_one]

theorem read_tensor_coordinate_at_origin (h : Polys V I) (v : V) (s : Mask I) :
    (∑ x, (outputTest node (layoutWord a b v) (dualMask (layoutWord a b v) s) x).eval 0 *
      tensorAt a b h v x 0) = (h (v,s)).eval 0 := by
  unfold tensorAt
  rw [dot_tensor_sum]
  simp only [output_test_origin_unchanged node,published_basis_dual]
  classical
  rw [Finset.sum_eq_single s]
  · simp
  · intro y _ hy
    rw [if_neg (Ne.symm hy),zero_mul]
  · simp

variable [DecidableEq V] [DecidableEq G]
variable {Rows : I → G → Type*} [∀ t g, Fintype (Rows t g)]
variable (Cmat : ∀ t g, Matrix (Rows t g) (GroupFiber (a t) g) ℚ)

/-- This is exactly the deleted-origin-coordinate condition proved
after (9), before the dimension increments are summed. -/
theorem forced_origin_coordinate_zero (P : Matrix V V ℚ[X]) (R j : ℕ)
    (inj : Function.Injective node) (nonzero : ∀ i, node i ≠ 0)
    (h0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (degree : ∀ u v, (P u v).natDegree ≤ R)
    (foreign : ∀ t u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (node t)) ∈
        Submodule.span ℚ (Set.range (Cmat t g).row))
    (h : FiltrationKernel node a b Cmat j) (v : V) (s : Mask I)
    (fits : R+j+weight (dualMask (layoutWord a b v) s) < Fintype.card I) :
    (h.val (v,s)).eval 0 = 0 := by
  let B := dualMask (layoutWord a b v) s
  have Hnorm := (mem_Ilt node a b Cmat (j+1) h.val).1 h.property
  have proof := matrix_tensor_certificate node a b Cmat P inj R j (weight B) h0 degree v
    (fun t g => foreign t v g) (tensorPolynomial a b h.val) (outputTest node (layoutWord a b v) B)
    (fun t u hlocal => by
      simp only [tensor_polynomial_eval]
      exact nodal_test_annihilates_allowed_tensor node a b j Hnorm.1 B v u t inj nonzero hlocal)
    (fun t g i x => by
      simp only [tensor_polynomial_eval,← full_nodal_check_coord]
      exact Hnorm.2 t g x i)
    (tensor_polynomial_degree node a b j Hnorm.1) (outputTest_degree node (layoutWord a b v) B) fits
  simp only [tensor_polynomial_eval,B,read_tensor_coordinate_at_origin] at proof
  exact proof

#print axioms tensor_polynomial_eval
#print axioms tensor_polynomial_degree
#print axioms low_basis_orthogonal_at_allowed_site
#print axioms nodal_test_annihilates_allowed_tensor
#print axioms read_tensor_coordinate_at_origin
#print axioms forced_origin_coordinate_zero
end
end Reconstruction.LayoutMismatch.PublishedFiltration

