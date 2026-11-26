import S8Certificates
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Prod

namespace S8

open scoped BigOperators

variable {P X A : Type*} [Fintype P] [Fintype X] [Fintype A] [Nonempty A]
  [DecidableEq P] [DecidableEq X]

/-- Splitting the independent primitive symbols into the chosen distinct
    positions and the unused positions. -/
noncomputable def restrictPrimitive (e : X ↪ P) :
    (P → A) ≃ (X → A) × ({p : P // p ∉ Set.range e} → A) := by
  classical
  let r : X ≃ Set.range e := Equiv.ofInjective e e.injective
  let p (x : P) := x ∈ Set.range e
  let h : X ⊕ {x : P // ¬ p x} ≃ P :=
    (Equiv.sumCongr r (Equiv.refl _)).trans (Equiv.sumCompl p)
  exact (h.symm.arrowCongr (Equiv.refl A)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

omit [Fintype P] [Fintype A] [Nonempty A] [DecidableEq X] in
theorem restrictPrimitive_fst (e : X ↪ P) (ω : P → A) :
    (restrictPrimitive e ω).1 = ω ∘ e := by
  ext x
  rfl

/-- An injective primitive index map has exactly the product-uniform
    marginal, irrespective of the unused positions. -/
theorem mean_restrict_primitive (e : X ↪ P) (f : (X → A) → ℚ) :
    ProductVariance.uniformMean (fun ω : P → A => f (ω ∘ e)) =
      ProductVariance.uniformMean f := by
  classical
  let equiv := restrictPrimitive (A := A) e
  have hr (ω : P → A) : f (ω ∘ e) = f (equiv ω).1 := by
    rw [restrictPrimitive_fst e ω]
  simp only [ProductVariance.uniformMean, ProductVariance.uniformWeight, hr]
  rw [equiv.sum_comp (fun v => f v.1), Fintype.sum_prod_type]
  have hcard := Fintype.card_congr equiv
  rw [Fintype.card_prod] at hcard
  rw [hcard]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_mul]
  have hp : (Fintype.card ({p : P // p ∉ Set.range e} → A) : ℚ) ≠ 0 := by positivity
  field_simp

variable [DecidableEq A]

theorem mean_diagonal :
    ProductVariance.uniformMean
      (fun z : (X → A) × (X → A) => if z.1 = z.2 then (1 : ℚ) else 0) =
        1 / Fintype.card (X → A) := by
  have h (x : X → A) : (∑ y : X → A, if x = y then (1 : ℚ) else 0) = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  simp only [ProductVariance.uniformMean, ProductVariance.uniformWeight, Fintype.card_prod,
    Fintype.sum_prod_type, h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.cast_mul]
  field_simp

/-- Two full cell labels agree with probability precisely the reciprocal of
    the cell count when their combined primitive positions are distinct. -/
theorem primitive_agreement (e f : X → P)
    (independent : Function.Injective (Sum.elim e f)) :
    (∑ ω : P → A, ProductVariance.uniformWeight (P → A) *
      (if ω ∘ e = ω ∘ f then (1 : ℚ) else 0)) = 1 / Fintype.card (X → A) := by
  let h : X ⊕ X ↪ P := ⟨Sum.elim e f, independent⟩
  let eqv := Equiv.sumArrowEquivProdArrow X X A
  let F (z : X ⊕ X → A) : ℚ := if (eqv z).1 = (eqv z).2 then 1 else 0
  have h1 := mean_restrict_primitive h F
  have h2 : ProductVariance.uniformMean F =
      ProductVariance.uniformMean (fun z : (X → A) × (X → A) =>
        if z.1 = z.2 then (1 : ℚ) else 0) := by
    unfold ProductVariance.uniformMean ProductVariance.uniformWeight
    rw [Fintype.card_congr eqv]
    congr 1
    exact eqv.sum_comp (fun z : (X → A) × (X → A) => if z.1 = z.2 then (1 : ℚ) else 0)
  simp only [← Finset.mul_sum]
  exact h1.trans (h2.trans mean_diagonal)

/-- The finite bad pairs may be exactly those sharing a primitive position.
    This specialization is usable for both placement constructions. -/
theorem primitive_collision_bound {W : Type*} [Fintype W] (site : W → X → P)
    (bad : Finset (W × W))
    (separate : ∀ e f, (e,f) ∉ bad → Function.Injective (Sum.elim (site e) (site f))) :
    (∑ ω : P → A, ProductVariance.uniformWeight (P → A) *
      collision (fun w => ω ∘ site w)) ≤ bad.card := by
  refine mean_collision_le _ ?_ (fun _ => by unfold ProductVariance.uniformWeight; positivity)
    _ bad (fun e f hef => primitive_agreement (site e) (site f) (separate e f hef))
  simp only [ProductVariance.uniformWeight, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by positivity)

#print axioms restrictPrimitive_fst
#print axioms mean_restrict_primitive
#print axioms primitive_agreement
#print axioms primitive_collision_bound

end S8

