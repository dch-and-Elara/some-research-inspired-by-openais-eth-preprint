import P2PublishedFiltrationSpaces

/-! Paper 2, Section 4, literal Eq. (9). The nodal kernel is
defined with every physical tensor coordinate. Its finite factorization
uses precisely the actual measurement ranges and one half mask per node. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open LayoutBudget (GroupFiber)
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V G : Type*} [Fintype I] [DecidableEq I]

/-- Evaluation in the common tensor coordinates, after changing from the
chosen basis e_{v,S}. No nodal vanishing or degree promise in this map. -/
def tensorAt (a b : I → V → G) [Fintype G] (h : Polys V I) (v : V) (x : Mask I)
    (z : ℚ) : ℚ :=
  ∑ s : Mask I, basisEntry (layoutWord a b v) s x * (h (v,s)).eval z

variable [Fintype G] [DecidableEq G]
variable (nodes : I → ℚ) (a b : I → V → G)
variable {Rows : I → G → Type*} [∀ t g, Fintype (Rows t g)]
variable (C : ∀ t g, Matrix (Rows t g) (GroupFiber (a t) g) ℚ)
variable [Fintype V]

def nodalEval (t : I) (g : G) (x : Mask I) :
    Polys V I →ₗ[ℚ] (GroupFiber (a t) g → ℚ) where
  toFun h v := tensorAt a b h v.val x (nodes t)
  map_add' h f := by
    funext v
    simp only [tensorAt, Pi.add_apply, eval_add, mul_add, Finset.sum_add_distrib]
  map_smul' c h := by
    funext v
    simp only [tensorAt, RingHom.id_apply, Pi.smul_apply, smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

/-- All coordinates of `(C_t ⊗ I_W)h(λ_t)`. Here the block diagonal
measurement is represented by its actual group matrices. -/
def fullNodalChecks :
    Polys V I →ₗ[ℚ] (∀ (t : I) (g : G), Mask I → Rows t g → ℚ) :=
  LinearMap.pi fun t => LinearMap.pi fun g => LinearMap.pi fun x =>
    (C t g).mulVecLin.comp (nodalEval nodes a b t g x)

theorem full_nodal_check_coord (h : Polys V I) (t : I) (g : G) (x : Mask I) (i : Rows t g) :
    fullNodalChecks nodes a b C h t g x i =
      ∑ v : GroupFiber (a t) g, C t g i v * tensorAt a b h v.val x (nodes t) := rfl

def Ilt (n : ℕ) : Submodule ℚ (Polys V I) :=
  Hlt nodes n ⊓ LinearMap.ker (fullNodalChecks nodes a b C)

abbrev FiltrationKernel (j : ℕ) := Ilt nodes a b C (j+1)

theorem mem_Ilt (n : ℕ) (h : Polys V I) :
    h ∈ Ilt nodes a b C n ↔ h ∈ Hlt nodes n ∧
      ∀ t g x i, fullNodalChecks nodes a b C h t g x i = 0 := by
  change (_ ∧ h ∈ LinearMap.ker _) ↔ _
  rw [LinearMap.mem_ker]
  refine and_congr_right (fun _ => ⟨?_,?_⟩)
  · intro z t g x i
    exact congrArg (fun out : ∀ (t : I) (g : G), Mask I → Rows t g → ℚ => out t g x i) z
  · intro z
    funext t g x i
    exact z t g x i

theorem high_coordinate_at_its_node_is_zero (n : ℕ) {h : Polys V I} (hh : h ∈ Hlt nodes n)
    (v : V) (s : Mask I) (t : I) (hs : s t = true) : (h (v,s)).eval (nodes t) = 0 := by
  obtain ⟨q,hq⟩ := ((mem_Hlt nodes n h).1 hh v s).2
  rw [hq, eval_mul, rootProduct_at_node nodes s t hs, zero_mul]

theorem tensorAt_nodal_half_factor (n : ℕ) {h : Polys V I} (hh : h ∈ Hlt nodes n)
    (t : I) (g : G) (v : GroupFiber (a t) g) (x : Mask I) :
    tensorAt a b h v.val x (nodes t) = lowFactor (groupSlope g) (x t) *
      tensorAt a b h v.val (extendZero t (fun i => x i.val)) (nodes t) := by
  unfold tensorAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s t = true
  · rw [high_coordinate_at_its_node_is_zero nodes n hh v.val s t hs, mul_zero, mul_zero, mul_zero]
  have hd : s t = false := Bool.eq_false_of_not_eq_true hs
  rw [basis_entry_half_split (layoutWord a b v.val) s x t hd, mul_assoc]
  have same : (layoutWord a b v.val t).1 = groupSlope g := congrArg groupSlope v.property
  rw [same]

theorem full_nodal_check_factors_through_half (n : ℕ) {h : Polys V I} (hh : h ∈ Hlt nodes n)
    (t : I) (g : G) (x : Mask I) (i : Rows t g) :
    fullNodalChecks nodes a b C h t g x i = lowFactor (groupSlope g) (x t) *
      fullNodalChecks nodes a b C h t g (extendZero t (fun j => x j.val)) i := by
  rw [full_nodal_check_coord, full_nodal_check_coord, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [tensorAt_nodal_half_factor nodes a b n hh t g v x]
  ring

abbrev HalfNodalTarget :=
  ∀ (t : I) (g : G), Half t → LinearMap.range (C t g).mulVecLin

def halfNodalChecks (n : ℕ) :
    Hlt (V:=V) nodes n →ₗ[ℚ] HalfNodalTarget a C :=
  LinearMap.pi fun t => LinearMap.pi fun g => LinearMap.pi fun x =>
    (C t g).mulVecLin.rangeRestrict.comp
      ((nodalEval nodes a b t g (extendZero t x)).comp (Hlt nodes n).subtype)

theorem half_nodal_check_coord (n : ℕ) (h : Hlt (V:=V) nodes n)
    (t : I) (g : G) (x : Half t) (i : Rows t g) :
    (halfNodalChecks nodes a b C n h t g x).val i =
      fullNodalChecks nodes a b C h.val t g (extendZero t x) i := rfl

theorem same_nodal_kernel (n : ℕ) (h : Hlt (V:=V) nodes n) :
    h ∈ LinearMap.ker (halfNodalChecks nodes a b C n) ↔ h.val ∈ Ilt nodes a b C n := by
  rw [LinearMap.mem_ker, mem_Ilt]
  constructor
  · intro zero
    refine ⟨h.property,?_⟩
    intro t g x i
    have hz := congrArg (fun data : HalfNodalTarget a C =>
      (data t g (fun j => x j.val)).val i) zero
    change (halfNodalChecks nodes a b C n h t g (fun j => x j.val)).val i = 0 at hz
    rw [half_nodal_check_coord] at hz
    rw [full_nodal_check_factors_through_half nodes a b C n h.property, hz, mul_zero]
  · rintro ⟨_,zero⟩
    funext t g x
    apply Subtype.ext
    funext i
    rw [half_nodal_check_coord]
    exact zero t g (extendZero t x) i

def exact_nodal_kernel_equiv (n : ℕ) :
    Ilt nodes a b C n ≃ₗ[ℚ] LinearMap.ker (halfNodalChecks nodes a b C n) where
  toFun h :=
    let h' : Hlt (V:=V) nodes n := ⟨h.val,h.property.1⟩
    ⟨h',(same_nodal_kernel nodes a b C n h').2 h.property⟩
  invFun h := ⟨h.val.val,(same_nodal_kernel nodes a b C n h.val).1 h.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem half_nodal_target_dimension :
    Module.finrank ℚ (HalfNodalTarget a C) =
      2^(Fintype.card I-1)*(∑ t, ∑ g, (C t g).rank) := by
  unfold HalfNodalTarget
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_half, ← Finset.mul_sum, Matrix.rank]
  simp

/-- Equation (9), in degree < n convention. No use of the final mismatch
bound, and no assumption about the ranks of the checks. -/
theorem nodal_kernel_codimension (n : ℕ) :
    Module.finrank ℚ (Hlt (V:=V) nodes n) - Module.finrank ℚ (Ilt nodes a b C n) ≤
      2^(Fintype.card I-1)*(∑ t, ∑ g, (C t g).rank) := by
  let L := halfNodalChecks nodes a b C n
  have e := (exact_nodal_kernel_equiv nodes a b C n).finrank_eq
  have h := L.finrank_range_add_finrank_ker
  have hb : Module.finrank ℚ (LinearMap.range L) ≤ Module.finrank ℚ (HalfNodalTarget a C) :=
    Submodule.finrank_le _
  rw [half_nodal_target_dimension a C] at hb
  change Module.finrank ℚ (Ilt nodes a b C n) = Module.finrank ℚ (LinearMap.ker L) at e
  rw [e]
  omega

theorem equation_nine (j : ℕ) (hk : 0 < Fintype.card I) :
    Module.finrank ℚ (H (V:=V) nodes j) - Module.finrank ℚ (FiltrationKernel nodes a b C j) ≤
      (2^Fintype.card I / 2)*(∑ t, ∑ g, (C t g).rank) := by
  have e : 2^Fintype.card I / 2 = 2^(Fintype.card I-1) := by
    obtain ⟨k,h⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [h,pow_succ]
    simp
  rw [e]
  exact nodal_kernel_codimension nodes a b C (j+1)

#print axioms full_nodal_check_coord
#print axioms mem_Ilt
#print axioms tensorAt_nodal_half_factor
#print axioms exact_nodal_kernel_equiv
#print axioms half_nodal_target_dimension
#print axioms nodal_kernel_codimension
#print axioms equation_nine
end
end Reconstruction.LayoutMismatch.PublishedFiltration

