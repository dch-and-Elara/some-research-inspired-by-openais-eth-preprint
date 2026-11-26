import P5MainBalanceM6Swaps
import P5MainBalanceM6Rows

/-! Finite Hamming support of the true source swap operators.
Support is measured on the ordered cell, ignoring repeated copies of
the same cell, which is sufficient for bounding mismatch corrections. -/
namespace P5MainBalance.M6
open P5MainIterator
open scoped BigOperators Classical

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def differences (u v : SwapSlot Copy I B) : Finset I :=
  Finset.univ.filter (fun i=>(phys u).2 i ≠ (phys v).2 i)

noncomputable def hcDist (u v : SwapSlot Copy I B) : ℕ := (differences u v).card

omit [Fintype Copy] [Fintype B] in
theorem hcDist_same (u : SwapSlot Copy I B) : hcDist u u=0 := by simp [hcDist,differences]

omit [Fintype Copy] [Fintype B] in
theorem hcDist_triangle (u v w : SwapSlot Copy I B) :
    hcDist u w≤hcDist u v+hcDist v w := by
  apply (Finset.card_le_card (show differences u w ⊆ differences u v ∪ differences v w from ?_)).trans
    (Finset.card_union_le _ _)
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  apply Finset.mem_union.mpr
  by_cases H : (phys u).2 i=(phys v).2 i
  · right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h' => h (H.trans h')⟩
  · left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem current_flip_one_coordinate (i j : I) (s : SwapSlot Copy I B) :
    (phys (flipAt i s)).2 j =
      if j=i then ((phys s).2 j).swap else (phys s).2 j := by
  by_cases he : j=i
  · subst j
    by_cases h : (s.1.2 i).val.1≠(s.1.2 i).val.2
    · unfold phys copyDecode decodeOrbit flipAt
      simp only [dif_pos h,ite_true]
      cases s.2 ⟨i,h⟩ <;> rfl
    · unfold phys copyDecode decodeOrbit flipAt
      simp only [dif_neg h,ite_true]
      exact Prod.ext (not_ne_iff.mp h) (not_ne_iff.mp h).symm
  · simp [phys,copyDecode,decodeOrbit,flipAt,he]

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem current_full_flip_coordinate (j : I) (s : SwapSlot Copy I B) :
    (phys (flipAll s)).2 j=((phys s).2 j).swap := by
  by_cases h : (s.1.2 j).val.1≠(s.1.2 j).val.2
  · unfold phys copyDecode decodeOrbit flipAll
    simp only [dif_pos h]
    cases s.2 ⟨j,h⟩ <;> rfl
  · unfold phys copyDecode decodeOrbit flipAll
    simp only [dif_neg h]
    exact Prod.ext (not_ne_iff.mp h) (not_ne_iff.mp h).symm

omit [Fintype Copy] [Fintype B] in
theorem one_flip_distance (i : I) (s : SwapSlot Copy I B) :
    hcDist s (flipAt i s) ≤ 1 := by
  have h : differences s (flipAt i s)⊆{i} := by
    intro j hj
    have H := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_singleton]
    by_contra hn
    exact H (by simp [current_flip_one_coordinate,hn])
  simpa only [hcDist,Finset.card_singleton] using Finset.card_le_card h

noncomputable def mismatch (u v : SwapSlot Copy I B) : Finset I :=
  Finset.univ.filter (fun i=> ((phys v).2 i).1 ≠ ((phys u).2 i).2)

omit [Fintype Copy] [Fintype B] in
theorem mismatch_at_most_swapped_dist (u v : SwapSlot Copy I B) :
    (mismatch u v).card≤hcDist (flipAll u) v := by
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro he
  apply (Finset.mem_filter.mp hi).2
  rw [current_full_flip_coordinate] at he
  exact (congrArg Prod.fst he).symm

#print axioms hcDist_triangle
#print axioms current_flip_one_coordinate
#print axioms current_full_flip_coordinate
#print axioms one_flip_distance
#print axioms mismatch_at_most_swapped_dist
end P5MainBalance.M6
