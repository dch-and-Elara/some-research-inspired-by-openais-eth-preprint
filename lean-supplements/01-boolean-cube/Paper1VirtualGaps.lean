import BooleanCube.RealBudget
import Mathlib.Data.Nat.Choose.Sum

/-! The sorted virtual-endpoint expression for (2) at the end of §3.
Both endpoints are shifted by one, making the virtual left endpoint zero.
An adjacent pair is encoded by the absence of intermediate endpoints. -/

namespace LocalReconstruction.Paper1Coverage

open Finset
noncomputable section

def printedVirtualEndpoints (q : ℕ) (K : Finset ℕ) : Finset ℕ :=
  insert 0 (insert (q+2) (K.image (·+1)))

def printedAdjacentPairs (q : ℕ) (K : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  let E := printedVirtualEndpoints q K
  exact (E.product E).filter fun p => p.1 < p.2 ∧
    ∀ z ∈ E, z ≤ p.1 ∨ p.2 ≤ z

@[simp] theorem mem_printedAdjacentPairs {q : ℕ} {K : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ printedAdjacentPairs q K ↔ p.1 ∈ printedVirtualEndpoints q K ∧
      p.2 ∈ printedVirtualEndpoints q K ∧ p.1 < p.2 ∧
      ∀ z ∈ printedVirtualEndpoints q K, z ≤ p.1 ∨ p.2 ≤ z := by
  classical
  simp [printedAdjacentPairs, and_assoc]

private theorem virtual_endpoint_bound {q : ℕ} {K : Finset ℕ} (hK : K ⊆ range (q+1))
    {k : ℕ} (hk : k ∈ printedVirtualEndpoints q K) : k ≤ q+2 := by
  simp only [printedVirtualEndpoints, mem_insert, mem_image] at hk
  rcases hk with rfl | rfl | ⟨j,hj,rfl⟩
  · omega
  · omega
  · have := mem_range.mp (hK hj)
    omega

theorem retained_interval_bounded_by_adjacent_endpoints {q L U : ℕ} {K : Finset ℕ}
    (hLU : L ≤ U) (hU : U ≤ q) (keep : ∀ j, L ≤ j → j ≤ U → j ∉ K) :
    ∃ p ∈ printedAdjacentPairs q K, p.1 ≤ L ∧ U+2 ≤ p.2 := by
  classical
  let E := printedVirtualEndpoints q K
  let lo := E.filter (· ≤ L)
  let hi := E.filter (U+2 ≤ ·)
  have h0 : 0 ∈ lo := by simp [lo,E,printedVirtualEndpoints]
  have hq : q+2 ∈ hi := by simp [hi,E,printedVirtualEndpoints]; omega
  let a := lo.max' ⟨0,h0⟩
  let b := hi.min' ⟨q+2,hq⟩
  obtain ⟨ha₁,ha₂⟩ := mem_filter.mp (lo.max'_mem ⟨0,h0⟩)
  obtain ⟨hb₁,hb₂⟩ := mem_filter.mp (hi.min'_mem ⟨q+2,hq⟩)
  change a ∈ E at ha₁
  change b ∈ E at hb₁
  change a ≤ L at ha₂
  change U+2 ≤ b at hb₂
  refine ⟨(a,b), mem_printedAdjacentPairs.mpr ⟨ha₁,hb₁,by omega,?_⟩, ha₂, hb₂⟩
  intro z hz
  by_cases left : z ≤ L
  · exact Or.inl (lo.le_max' _ (mem_filter.mpr ⟨hz,left⟩))
  by_cases right : U+2 ≤ z
  · exact Or.inr (hi.min'_le _ (mem_filter.mpr ⟨hz,right⟩))
  change z ∈ E at hz
  simp only [E, printedVirtualEndpoints, mem_insert, mem_image] at hz
  rcases hz with h | h | ⟨j,hj,rfl⟩
  · omega
  · omega
  exact (keep j (by omega) (by omega) hj).elim

def printedVirtualWidth (q : ℕ) (K : Finset ℕ) : ℕ :=
  (printedAdjacentPairs q K).sup (fun p => p.2-p.1)

/-- The exact virtual-endpoint formula in natural subtraction. The
all-deleted harmless edge case is represented by a zero maximum gap. -/
theorem gap_eq_printed_virtual_width {q : ℕ} {K : Finset ℕ} (hK : K ⊆ range (q+1)) :
    maxGap q K = printedVirtualWidth q K-2 := by
  apply le_antisymm
  · apply (maxGap_le_iff q _ K).mpr
    intro L U hLU hU keep
    obtain ⟨p,hp,ha,hb⟩ := retained_interval_bounded_by_adjacent_endpoints hLU hU keep
    have hpw : p.2-p.1 ≤ printedVirtualWidth q K := le_sup (f := fun p : ℕ × ℕ => p.2-p.1) hp
    omega
  · suffices h : printedVirtualWidth q K ≤ maxGap q K+2 by omega
    apply Finset.sup_le_iff.mpr
    intro p hp
    obtain ⟨_,hb,_,adj⟩ := mem_printedAdjacentPairs.mp hp
    have hq := virtual_endpoint_bound hK hb
    by_cases small : p.2 < p.1+2
    · omega
    have hgap := (maxGap_le_iff q (maxGap q K) K).mp le_rfl
    have keep : ∀ j, p.1 ≤ j → j ≤ p.2-2 → j ∉ K := by
      intro j h1 h2 hj
      have hm : j+1 ∈ printedVirtualEndpoints q K :=
        mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hj))
      have h := adj (j+1) hm
      omega
    have ho := hgap p.1 (p.2-2) (by omega) (by omega) keep
    omega

/-- On the paper's domain with a retained layer, no truncation is needed:
the signed formula is literally largest adjacent gap minus two. -/
theorem signed_gap_eq_printed_virtual_width {q : ℕ} {K : Finset ℕ}
    (hK : K ⊆ range (q+1)) (hasRetained : ∃ j ≤ q, j ∉ K) :
    (maxGap q K : ℤ) = (printedVirtualWidth q K : ℤ)-2 := by
  obtain ⟨j,hj,hret⟩ := hasRetained
  obtain ⟨p,hp,hp₁,hp₂⟩ := retained_interval_bounded_by_adjacent_endpoints
    (L := j) (U := j) le_rfl hj (fun k h₁ h₂ => by rwa [show k = j by omega])
  have hw : p.2-p.1 ≤ printedVirtualWidth q K := le_sup (f := fun p : ℕ × ℕ => p.2-p.1) hp
  have hge : 2 ≤ printedVirtualWidth q K := by omega
  rw [gap_eq_printed_virtual_width hK, Nat.cast_sub hge]
  rfl

/-- The original budget is strictly below the cost of deleting the whole cube. -/
theorem original_budget_keeps_a_layer {q : ℕ} {γ : ℝ} (hq : 2 ≤ q) (hγ : 0 < γ)
    {K : Finset ℕ} (hK : K ⊆ range (q+1))
    (cost : ((∑ j ∈ K, q.choose j : ℕ) : ℝ) ≤ measurementBudget q γ) :
    ∃ j ≤ q, j ∉ K := by
  by_contra! hall
  have eq : K = range (q+1) := Subset.antisymm hK fun j hj =>
    hall j (Nat.le_of_lt_succ (mem_range.mp hj))
  rw [eq, Nat.sum_range_choose] at cost
  push_cast at cost
  have hstrict : measurementBudget q γ < (2:ℝ)^q := by
    unfold measurementBudget
    exact div_lt_self (by positivity) (Real.one_lt_rpow (by exact_mod_cast (show 1 < q by omega)) hγ)
  exact (not_le_of_gt hstrict) cost

/-- At integer budget at least `2^q` there is a degree-zero scheme, including
for the more general distinct nonzero labels of the public finite proof. -/
theorem full_walsh_budget_degree_zero {q b : ℕ} {a : Fin q → ℚ}
    (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0) (hb : 2^q ≤ b) :
    symmetricScheme q b 0 a := by
  apply (symmetric_budget_iff ha hn).mpr
  refine ⟨range (q+1), subset_rfl, (Nat.sum_range_choose q).trans_le hb, ?_⟩
  intro L U hLU hU hclear
  exact (hclear L le_rfl hLU (mem_range.mpr (Nat.lt_succ_of_le (hLU.trans hU)))).elim

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.mem_printedAdjacentPairs
#print axioms LocalReconstruction.Paper1Coverage.retained_interval_bounded_by_adjacent_endpoints
#print axioms LocalReconstruction.Paper1Coverage.gap_eq_printed_virtual_width
#print axioms LocalReconstruction.Paper1Coverage.signed_gap_eq_printed_virtual_width
#print axioms LocalReconstruction.Paper1Coverage.original_budget_keeps_a_layer
#print axioms LocalReconstruction.Paper1Coverage.full_walsh_budget_degree_zero
