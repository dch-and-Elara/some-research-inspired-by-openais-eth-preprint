import Paper1Eq18

/-! Paper 1, §6.1: the exact kernel of evaluation on the original `I_j`
and the rank-nullity sum for the paper's `V_j`. -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The actual polynomial coordinate of a spline vanishing on the deleted family. -/
def vanishingPolynomial {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) (x : Cube q) : ℚ[X] :=
  (h.val.val x).val

theorem vanishingPolynomial_injective {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)} :
    Function.Injective (@vanishingPolynomial q k a A) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact Subtype.ext (congrFun h x)

theorem vanishingPolynomial_degree {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) (x : Cube q) :
    (vanishingPolynomial h x).natDegree ≤ k := by
  by_cases hz : vanishingPolynomial h x = 0
  · simp [hz]
  have hlt := mem_degreeLT.mp (h.val.val x).property
  change (vanishingPolynomial h x).degree < ↑(k+1) at hlt
  rw [degree_eq_natDegree hz] at hlt
  exact Nat.le_of_lt_succ (WithBot.coe_lt_coe.mp hlt)

theorem vanishingPolynomial_edges {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) : EqualEdges a (vanishingPolynomial h) :=
  h.val.property

theorem vanishingPolynomial_deleted {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) : ∀ x ∈ A, vanishingPolynomial h x = 0 :=
  (mem_vanishingSplines_iff h.val).mp h.property

/-- Membership constructor for the same vanishing spline, not a different model. -/
def ofVanishingFamily {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (f : Cube q → ℚ[X]) (deg : ∀ x, (f x).natDegree ≤ k)
    (edges : EqualEdges a f) (zero : ∀ x ∈ A, f x = 0) : vanishingSplines a k A := by
  let g : Cube q → Bounded (k+1) := fun x =>
    ⟨f x, mem_degreeLT.mpr (lt_of_le_of_lt degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (deg x))))⟩
  let u : splines a k := ⟨g, edges⟩
  exact ⟨u, (mem_vanishingSplines_iff u).mpr zero⟩

@[simp] theorem ofVanishingFamily_apply {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (f : Cube q → ℚ[X]) (deg : ∀ x, (f x).natDegree ≤ k)
    (edges : EqualEdges a f) (zero : ∀ x ∈ A, f x = 0) (x : Cube q) :
    vanishingPolynomial (ofVanishingFamily f deg edges zero) x = f x := rfl

/-- Coordinatewise evaluation at the literal reconstruction point zero. -/
def evalVanishing {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    vanishingSplines a k A →ₗ[ℚ] (Cube q → ℚ) :=
  LinearMap.pi fun x => (sample (0:ℚ)).comp
    ((LinearMap.proj (R := ℚ) x).comp ((splines a k).subtype.comp (vanishingSplines a k A).subtype))

@[simp] theorem evalVanishing_apply {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) (x : Cube q) :
    evalVanishing a k A h x = (vanishingPolynomial h x).eval 0 := rfl

/-- The paper's evaluation image `V_k`. -/
def vanishingImage {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    Submodule ℚ (Cube q → ℚ) :=
  LinearMap.range (evalVanishing a k A)

/-- The concrete multiplication-by-`X` map between successive degree cutoffs. -/
def shiftVanishingX {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    vanishingSplines a k A →ₗ[ℚ] vanishingSplines a (k+1) A where
  toFun h := ofVanishingFamily (fun x => X * vanishingPolynomial h x) (by
    intro x
    apply natDegree_mul_le.trans
    rw [natDegree_X]
    have hd := vanishingPolynomial_degree h x
    omega) (by
    intro i x
    simp only [eval_mul, eval_X, vanishingPolynomial_edges h i x]) (by
    intro x hx
    simp [vanishingPolynomial_deleted h x hx])
  map_add' h g := by
    apply vanishingPolynomial_injective
    funext x
    change X * (vanishingPolynomial h x + vanishingPolynomial g x) =
      X * vanishingPolynomial h x + X * vanishingPolynomial g x
    exact mul_add _ _ _
  map_smul' c h := by
    apply vanishingPolynomial_injective
    funext x
    change X * (c • vanishingPolynomial h x) = c • (X * vanishingPolynomial h x)
    simp only [smul_eq_C_mul]
    exact mul_left_comm _ _ _

@[simp] theorem shiftVanishingX_apply {q k : ℕ} {a : Fin q → ℚ} {A : Finset (Cube q)}
    (h : vanishingSplines a k A) (x : Cube q) :
    vanishingPolynomial (shiftVanishingX a k A h) x = X * vanishingPolynomial h x := rfl

theorem shiftVanishingX_injective {q : ℕ} (a : Fin q → ℚ) (k : ℕ) (A : Finset (Cube q)) :
    Function.Injective (shiftVanishingX a k A) := by
  intro h g eq
  apply vanishingPolynomial_injective
  funext x
  apply mul_left_cancel₀ X_ne_zero
  exact congrArg (fun u => vanishingPolynomial u x) eq

/-- Exactly the printed assertion `ker(eval₀ : I_{k+1} → ...) = X I_k`.
Every label being nonzero is used when dividing by `X`. -/
theorem evaluation_kernel_eq_shiftX {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (k : ℕ) (A : Finset (Cube q)) :
    LinearMap.ker (evalVanishing a (k+1) A) = LinearMap.range (shiftVanishingX a k A) := by
  apply le_antisymm
  · intro u hu
    apply LinearMap.mem_range.mpr
    have hcoeff (x : Cube q) : (vanishingPolynomial u x).coeff 0 = 0 := by
      simpa only [← evalVanishing_apply, coeff_zero_eq_eval_zero] using
        congrFun (LinearMap.mem_ker.mp hu) x
    have fact (x : Cube q) : X * (vanishingPolynomial u x).divX = vanishingPolynomial u x := by
      simpa [hcoeff x] using X_mul_divX_add (vanishingPolynomial u x)
    let h : vanishingSplines a k A :=
      ofVanishingFamily (fun x => (vanishingPolynomial u x).divX) (by
        intro x
        rw [natDegree_divX_eq_natDegree_tsub_one]
        have hd := vanishingPolynomial_degree u x
        omega) (by
        intro i x
        apply mul_left_cancel₀ (hn i)
        have e := vanishingPolynomial_edges u i x
        rw [← fact x, ← fact (flip i x), eval_mul, eval_mul, eval_X] at e
        exact e) (by
        intro x hx
        simp [vanishingPolynomial_deleted u x hx])
    refine ⟨h, vanishingPolynomial_injective ?_⟩
    funext x
    exact fact x
  · intro u hu
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
    apply LinearMap.mem_ker.mpr
    funext x
    simp

/-- The degree-zero case represents the paper's convention `I_{-1}=0`. -/
theorem evaluation_kernel_zero {q : ℕ} (a : Fin q → ℚ) (A : Finset (Cube q)) :
    LinearMap.ker (evalVanishing a 0 A) = ⊥ := by
  apply le_antisymm _ bot_le
  intro h he
  change h = 0
  apply vanishingPolynomial_injective
  funext x
  change vanishingPolynomial h x = 0
  have hcoeff : (vanishingPolynomial h x).coeff 0 = 0 := by
    simpa only [← evalVanishing_apply, coeff_zero_eq_eval_zero] using
      congrFun (LinearMap.mem_ker.mp he) x
  rw [eq_C_of_natDegree_le_zero (vanishingPolynomial_degree h x), hcoeff, C_0]

theorem evaluation_kernel_dimension_succ {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (k : ℕ) (A : Finset (Cube q)) :
    Module.finrank ℚ (LinearMap.ker (evalVanishing a (k+1) A)) =
      Module.finrank ℚ (vanishingSplines a k A) := by
  rw [evaluation_kernel_eq_shiftX hn]
  exact (LinearEquiv.ofInjective (shiftVanishingX a k A) (shiftVanishingX_injective a k A)).finrank_eq.symm

/-- The exact dimension sum at lines 580–584 of the published manuscript. -/
theorem vanishing_dimension_sum {q : ℕ} {a : Fin q → ℚ} (hn : ∀ i, a i ≠ 0)
    (K : ℕ) (A : Finset (Cube q)) :
    Module.finrank ℚ (vanishingSplines a K A) =
      ∑ j ∈ Finset.range (K+1), Module.finrank ℚ (vanishingImage a j A) := by
  letI (j : ℕ) : AddCommGroup ↥(splines a j) := (splines a j).addCommGroup
  letI (j : ℕ) : AddCommGroup ↥(vanishingSplines a j A) := (vanishingSplines a j A).addCommGroup
  induction K with
  | zero =>
    have hr := LinearMap.finrank_range_add_finrank_ker (K := ℚ)
      (V := ↥(vanishingSplines a 0 A)) (V₂ := (Cube q → ℚ)) (evalVanishing a 0 A)
    rw [evaluation_kernel_zero, finrank_bot, Nat.add_zero] at hr
    simpa [vanishingImage] using hr.symm
  | succ K ih =>
    have hr := LinearMap.finrank_range_add_finrank_ker (K := ℚ)
      (V := ↥(vanishingSplines a (K+1) A)) (V₂ := (Cube q → ℚ)) (evalVanishing a (K+1) A)
    rw [evaluation_kernel_dimension_succ hn, ih] at hr
    rw [Finset.sum_range_succ]
    exact hr.symm.trans (Nat.add_comm _ _)

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.vanishingPolynomial_injective
#print axioms LocalReconstruction.Paper1Coverage.vanishingPolynomial_degree
#print axioms LocalReconstruction.Paper1Coverage.vanishingPolynomial_edges
#print axioms LocalReconstruction.Paper1Coverage.vanishingPolynomial_deleted
#print axioms LocalReconstruction.Paper1Coverage.ofVanishingFamily_apply
#print axioms LocalReconstruction.Paper1Coverage.evalVanishing_apply
#print axioms LocalReconstruction.Paper1Coverage.shiftVanishingX_apply
#print axioms LocalReconstruction.Paper1Coverage.shiftVanishingX_injective
#print axioms LocalReconstruction.Paper1Coverage.evaluation_kernel_eq_shiftX
#print axioms LocalReconstruction.Paper1Coverage.evaluation_kernel_zero
#print axioms LocalReconstruction.Paper1Coverage.evaluation_kernel_dimension_succ
#print axioms LocalReconstruction.Paper1Coverage.vanishing_dimension_sum
