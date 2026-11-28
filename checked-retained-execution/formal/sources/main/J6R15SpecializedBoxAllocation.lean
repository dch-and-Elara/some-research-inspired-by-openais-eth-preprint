import J6R15SpecializedBoxPacketSingleton
import J9R15FrozenErasureProjection
import J6PacketCoefficientBridge

/-! Expand the genuine fixed projection at a *single* nonzero exponent.
Exactly one actual row leg is marked. No menus are pruned, and no
output coefficient is assumed to have been physically realized. -/
namespace J6R14SpecializedBox
open scoped BigOperators Classical
open MvPolynomial J6PacketCoefficientBridge

noncomputable section
variable {R I M : Type*} [CommRing R] [Fintype I] [Fintype M]

omit [Fintype M] in
private theorem singleOne_ne_zero (m : M) : Finsupp.single m (1:ℕ) ≠ 0 := by
  classical
  intro he
  have hc := congrArg (fun x : M→₀ℕ => x m) he
  simp at hc

omit [Fintype M] in
private theorem different_single (m j : M) (h : m≠j) :
    Finsupp.single m (1:ℕ) ≠ Finsupp.single j 1 := by
  classical
  intro he
  have hc := congrArg (fun x : M→₀ℕ => x m) he
  simp [h] at hc

def slotRow (f : Option M→R) : MvPolynomial M R :=
  ∑ v : Option M, monomial (J6PacketCoefficientBridge.exponent v) (f v)

private theorem slotRow_coeff0 (f : Option M→R) : coeff 0 (slotRow f) = f none := by
  classical
  rw [slotRow,Fintype.sum_option,coeff_add,coeff_sum]
  simp [J6PacketCoefficientBridge.exponent,coeff_monomial]

private theorem slotRow_single (f : Option M→R) (m : M) :
    coeff (Finsupp.single m 1) (slotRow f) = f (some m) := by
  classical
  rw [slotRow,Fintype.sum_option,coeff_add,coeff_sum]
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _)]
  · simp [J6PacketCoefficientBridge.exponent,coeff_monomial,Ne.symm (singleOne_ne_zero m)]
  · intro n _ hn
    simp [J6PacketCoefficientBridge.exponent,coeff_monomial,different_single _ _ hn]

theorem allocation_exact_one (f : I→Option M→R) (m : M) :
    (∑ α : I→Option M, if J9R15FrozenErasureProjection.allocationExponent α = Finsupp.single m 1 then
      ∏ e, f e (α e) else 0) =
    ∑ e : I, f e (some m) * ∏ j ∈ (Finset.univ : Finset I).erase e, f j none := by
  classical
  trans coeff (Finsupp.single m 1) (∏ e, slotRow (f e))
  · symm
    rw [show (∏ e,slotRow (f e)) =
      ∏ e, ∑ v : Option M, monomial (J6PacketCoefficientBridge.exponent v) (f e v) from rfl,
      coeff_allocations]
    refine Finset.sum_congr rfl ?_
    intro α _
    have he : J9R15FrozenErasureProjection.allocationExponent α = Finsupp.single m 1 ↔
        ∀ k, J6ActiveProfile.count α k = Finsupp.single m 1 k := by
      constructor
      · intro h k
        rw [← J9R15FrozenErasureProjection.allocation_count,h]
      · intro h
        ext k
        rw [J9R15FrozenErasureProjection.allocation_count,h]
    by_cases h : J9R15FrozenErasureProjection.allocationExponent α = Finsupp.single m 1
    · rw [if_pos h,if_pos (he.mp h)]
    · rw [if_neg h,if_neg (fun H => h (he.mpr H))]
  · simp only [mv_single_prod,slotRow_single,slotRow_coeff0]

#print axioms allocation_exact_one
end
end J6R14SpecializedBox
