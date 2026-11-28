import V8CapacityFactorial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Basic

/-! The native DVR Newton factors normalize over the base ring itself.
Every grid coefficient is protected against extra loss; the grid's
unimodularity and A2's evaluation factorization follow. -/
namespace V8CapacityNewtonGrid
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityFactorial

noncomputable section
set_option linter.unusedSectionVars false

variable {O : Type*} [CommRing O] [IsDomain O] {π : O} {q : ℕ}
variable (D : Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)

def norm (n : ℕ) (x : O) : O :=
  Classical.choose (newton_divisor D hq hq₂ h0 hπ n x)

theorem norm_factor (n : ℕ) (x : O) :
    newton D hq n x=π^debt q n*norm D hq hq₂ h0 hπ n x :=
  Classical.choose_spec (newton_divisor D hq hq₂ h0 hπ n x)

theorem norm_below (n r : ℕ) (hr : r<n) : norm D hq hq₂ h0 hπ n (node D hq r)=0 := by
  have hZ : newton D hq n (node D hq r)=0 := by
    unfold newton
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨r,hr⟩ : Fin n)) (by exact sub_self _)
  have h := (norm_factor D hq hq₂ h0 hπ n (node D hq r)).symm.trans hZ
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hπ)

variable [IsLocalRing O]
variable (hMax : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))

include hMax in
theorem norm_diag (n : ℕ) : IsUnit (norm D hq hq₂ h0 hπ n (node D hq n)) := by
  obtain ⟨u,hu⟩ := newton_diagonal_unit D hq hq₂ h0 hπ hMax n
  have h := (norm_factor D hq hq₂ h0 hπ n (node D hq n)).symm.trans hu
  have he := mul_left_cancel₀ (pow_ne_zero _ hπ) h
  rw [he]
  exact u.isUnit

variable {E I Y : Type*} [Fintype E] [Fintype I]

def tensor (degree : E → ℕ) (x : E → O) : O :=
  ∏ e : E, newton D hq (degree e) (x e)

def tensorNorm (degree : E → ℕ) (x : E → O) : O :=
  ∏ e : E, norm D hq hq₂ h0 hπ (degree e) (x e)

def multiDebt (q : ℕ) (ν : E → ℕ) : ℕ :=
  ∑ e : E, debt q (ν e)

theorem tensor_factor (degree : E → ℕ) (x : E → O) :
    tensor D hq degree x=π^multiDebt q degree*tensorNorm D hq hq₂ h0 hπ degree x := by
  simp only [tensor,tensorNorm,multiDebt,norm_factor D hq hq₂ h0 hπ,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

def nodeAt (degree : I → E → ℕ) (i : I) : E → O := fun e => node D hq (degree i e)

def normGrid (degree : I → E → ℕ) : Matrix I I O :=
  Matrix.of fun r c => tensorNorm D hq hq₂ h0 hπ (degree c) (nodeAt D hq degree r)

theorem weighted_evaluation (degree : I → E → ℕ) (C : Matrix I Y O) :
    (Matrix.of fun r y => ∑ i : I, tensor D hq (degree i) (nodeAt D hq degree r)*C i y) =
      normGrid D hq hq₂ h0 hπ degree *
        (Matrix.of fun i y => π^multiDebt q (degree i)*C i y) := by
  ext r y
  simp only [Matrix.mul_apply,Matrix.of_apply,normGrid,tensor_factor D hq hq₂ h0 hπ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ac_rfl

variable [LinearOrder I]

include hMax in
theorem norm_grid_unit (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j) :
    IsUnit (normGrid D hq hq₂ h0 hπ degree).det := by
  have low : (normGrid D hq hq₂ h0 hπ degree).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i<j at hij
    obtain ⟨e,he⟩ := not_forall.mp
      (fun h : ∀ e, degree j e≤degree i e => (not_le_of_gt hij) (order j i h))
    exact Finset.prod_eq_zero (Finset.mem_univ e)
      (norm_below D hq hq₂ h0 hπ _ _ (lt_of_not_ge he))
  rw [Matrix.det_of_lowerTriangular _ low]
  apply IsUnit.prod_univ_iff.mpr
  intro i
  change IsUnit (tensorNorm D hq hq₂ h0 hπ (degree i) (nodeAt D hq degree i))
  apply IsUnit.prod_univ_iff.mpr
  intro e
  exact norm_diag D hq hq₂ h0 hπ hMax (degree i e)

def evalNormalized (degree : I → E → ℕ) (c : I → O) (x : E → O) : O :=
  ∑ i : I, tensorNorm D hq hq₂ h0 hπ (degree i) x*c i

include hMax in
theorem all_values_iff_newton_coeff (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j) (J : Ideal O) (c : I → O) :
    (∀ x, evalNormalized D hq hq₂ h0 hπ degree c x∈J) ↔ ∀ i, c i∈J := by
  constructor
  · intro hv i
    let G := normGrid D hq hq₂ h0 hπ degree
    have hDet : IsUnit G.det := norm_grid_unit D hq hq₂ h0 hπ hMax degree order
    have hBack : G⁻¹.mulVec (G.mulVec c)=c := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul G hDet,Matrix.one_mulVec]
    rw [← hBack]
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (hv (nodeAt D hq degree j)))
  · intro hc x
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (hc j))

#print axioms norm_factor
#print axioms norm_below
#print axioms norm_diag
#print axioms tensor_factor
#print axioms weighted_evaluation
#print axioms norm_grid_unit
#print axioms all_values_iff_newton_coeff
end
end V8CapacityNewtonGrid
