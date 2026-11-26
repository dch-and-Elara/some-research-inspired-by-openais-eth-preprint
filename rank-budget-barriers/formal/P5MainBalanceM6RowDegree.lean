import P5MainBalanceM6Distance

/-! From the exact swap support to the paper's degree bound. The
coordinate mismatch roots in φ are the only possible positive degrees. -/
namespace P5MainBalance.M6
open P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

omit [Fintype Copy] [Fintype B] in
theorem atNode_degree_le_mismatches (t : I→ℚ) (u v : Slt Copy I B) :
    (atNode t u v).natDegree≤(mismatch u v).card := by
  have he : atNode t u v=∏ i∈mismatch u v, (1-X*C (t i)⁻¹) := by
    unfold atNode mismatch
    rw [Finset.prod_filter]
    exact Finset.prod_congr rfl (fun i _=>by split <;> simp_all)
  have hAtom (i : I) : (1-X*C (t i)⁻¹ : ℚ[X]).natDegree≤1 := by
    have hA : (1:ℚ[X]).natDegree≤1 := by simp
    have hB : (X*C (t i)⁻¹:ℚ[X]).natDegree≤1 :=
      natDegree_mul_le_of_le (by simp : (X:ℚ[X]).natDegree≤1)
        (by simp : (C (t i)⁻¹:ℚ[X]).natDegree≤0)
    simpa only [max_self] using natDegree_sub_le_of_le hA hB
  rw [he]
  calc
    _ ≤ ∑ i∈mismatch u v,(1-X*C (t i)⁻¹:ℚ[X]).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i∈mismatch u v,1 := Finset.sum_le_sum (fun i _=>hAtom i)
    _ = _ := by simp

theorem rowChart_degree_from_support (t : I→ℚ) (M : Mix Copy I B)
    (d : ℕ) (hM : ∀ u v,d<(mismatch u v).card → M u v=0)
    (u : Slt Copy I B) (ζ : Vec Copy I B) :
    (rowChart t M u ζ).natDegree≤d := by
  unfold rowChart
  apply (natDegree_add_le _ _).trans
  apply max_le
  · simp
  apply natDegree_sum_le_of_forall_le
  intro v _
  by_cases h : d<(mismatch u v).card
  · rw [hM u v h,zero_mul,map_zero,zero_mul,natDegree_zero]
    omega
  · have hv : (mismatch u v).card≤d := by omega
    simpa only [Nat.zero_add] using natDegree_mul_le_of_le
      (by rw [natDegree_C] : (C (M u v*ζ v):ℚ[X]).natDegree ≤ 0)
      ((atNode_degree_le_mismatches t u v).trans hv)

theorem physicalRow_degree_from_support (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (d : ℕ) (hM : ∀ u v,d<(mismatch u v).card → M u v=0)
    (e : E) (x : W→ℚ) :
    (physicalRow L t M e x).natDegree≤d :=
  rowChart_degree_from_support t M d hM (slotOf L e) (place L x)

#print axioms atNode_degree_le_mismatches
#print axioms rowChart_degree_from_support
#print axioms physicalRow_degree_from_support
end P5MainBalance.M6
