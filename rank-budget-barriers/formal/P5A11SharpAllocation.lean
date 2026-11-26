import P5A11SharpSlots
import P5A11SharpFibres

/-! Construct the coordinate exponents for all nonuniform precisions;
each layer achieves exactly the minimum of the selected budget and
the number of live slots. -/
namespace Paper5
open scoped BigOperators Classical

variable {T : Type*} [Fintype T] [LinearOrder T]

noncomputable def selectedExponent (P k : T→ℕ) (d : ℕ) (u : T) : ℕ :=
  ((topSlots P k d).filter (fun x=>x.1=u)).card

theorem selectedExponent_le (P k : T→ℕ) (d : ℕ) (u : T) :
    selectedExponent P k d u≤k u :=
  selected_node_fiber_card_le k (topSlots P k d) u

theorem topSlots_card_exact (P k : T→ℕ) (d : ℕ) (h : d≤∑ u,k u) :
    (topSlots P k d).card=d := by
  unfold topSlots
  rw [List.toFinset_card_of_nodup ((slotsSorted_nodup P k).take : ((slotsSorted P k).take d).Nodup),List.length_take]
  have he : (slotsSorted P k).length=∑ u,k u := by
    unfold slotsSorted
    rw [Finset.length_sort,Finset.card_univ,Fintype.card_sigma]
    simp only [Fintype.card_fin]
  rw [he,min_eq_left h]

theorem selectedExponent_sum (P k : T→ℕ) (d : ℕ) (h : d≤∑ u,k u) :
    (∑ u,selectedExponent P k d u)=d := by
  unfold selectedExponent
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simpa using topSlots_card_exact P k d h

theorem selectedExponent_layer (P k : T→ℕ) (d j : ℕ) :
    (∑ u ∈ Finset.univ.filter (fun u=>j<P u), selectedExponent P k d u) =
      min d (∑ u ∈ Finset.univ.filter (fun u=>j<P u),k u) := by
  unfold selectedExponent
  rw [←selected_slot_filter_by_node k (topSlots P k d) (fun u=>j<P u)]
  rw [topSlots_filter_count,whole_slot_filter_by_node k (fun u=>j<P u)]

theorem also_exists_sharp_slots (P k : T→ℕ) (d : ℕ) (h : d≤∑u,k u) :
    ∃ l : T→ℕ, (∀ u,l u≤k u) ∧ (∑u,l u)=d ∧
      ∀ j : ℕ,(∑u ∈ Finset.univ.filter (fun u=>j<P u),l u)=
        min d (∑u ∈ Finset.univ.filter (fun u=>j<P u),k u) :=
  ⟨selectedExponent P k d,selectedExponent_le P k d,selectedExponent_sum P k d h,
   selectedExponent_layer P k d⟩

#print axioms selectedExponent_le
#print axioms topSlots_card_exact
#print axioms selectedExponent_sum
#print axioms selectedExponent_layer
#print axioms also_exists_sharp_slots
end Paper5
