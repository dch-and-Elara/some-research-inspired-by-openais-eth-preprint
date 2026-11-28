import V8CapacityIntegrated

/-! Finite A4 witnessing restriction: the actual Newton grid determines
all residues on the full chart, for each prescribed ideal. -/
namespace V8CapacityGridDetermines
open scoped Classical BigOperators
open V8CapacityDigits V8CapacityNewtonGrid V8CapacityIntegrated

noncomputable section
set_option linter.unusedSectionVars false

variable {O E I : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Fintype E] [Fintype I] [LinearOrder I]
variable {π : O} {q : ℕ}
variable (D : Digits π q) (hq : 0<q) (hq₂ : 2≤q)
variable (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0)
variable (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O))
variable (degree : I → E → ℕ)
variable (order : ∀ i j, (∀ e, degree i e≤degree j e) → i≤j)

include hMax order in
theorem grid_ideal_iff (J : Ideal O) (v : I → O) :
    (∀ i : I, evalNormalized D hq hq₂ h0 hπ degree v (nodeAt D hq degree i) ∈ J) ↔
    (∀ x : E → O, evalNormalized D hq hq₂ h0 hπ degree v x ∈ J) := by
  constructor
  · intro agree
    have h := all_values_iff_newton_coeff D hq hq₂ h0 hπ hMax degree order J v
    apply h.mpr
    let G := normGrid D hq hq₂ h0 hπ degree
    have hDet : IsUnit G.det := norm_grid_unit D hq hq₂ h0 hπ hMax degree order
    have hBack : (G⁻¹).mulVec (G.mulVec v)=v := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul G hDet,Matrix.one_mulVec]
    intro i
    rw [← hBack]
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (agree j))
  · intro h i
    exact h (nodeAt D hq degree i)

include hMax order in
theorem grid_residue_iff (J : Ideal O) (v w : I → O) :
    (∀ i : I, Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree v (nodeAt D hq degree i)) =
      Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree w (nodeAt D hq degree i))) ↔
    (∀ x : E → O, Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree v x) =
      Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree w x)) := by
  have h (x : E → O) :
      Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree v x) =
        Ideal.Quotient.mk J (evalNormalized D hq hq₂ h0 hπ degree w x) ↔
      evalNormalized D hq hq₂ h0 hπ degree (fun i => v i-w i) x∈J := by
    have hh := eval_difference D hq hq₂ h0 hπ degree v w 1 x
    simp only [one_mul] at hh
    rw [← hh,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero]
  simp_rw [h]
  exact grid_ideal_iff D hq hq₂ h0 hπ hMax degree order J (fun i => v i-w i)

#print axioms grid_ideal_iff
#print axioms grid_residue_iff
end
end V8CapacityGridDetermines

