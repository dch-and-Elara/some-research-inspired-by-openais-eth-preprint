import F5R61CycleOrder

namespace F5R61
set_option autoImplicit false

theorem orderedSlots_of_two_or_more {P : Type} (ps : List (P × P)) (extra : List P)
    (h : 2 ≤ ps.length) :
    orderedSlots ps extra = (ps.map Prod.fst ++ ps.map Prod.snd) ++ extra := by
  cases ps with
  | nil => simp at h
  | cons p rest =>
    cases rest with
    | nil => simp at h
    | cons q qs => simp [orderedSlots,List.append_assoc]

theorem actual_two_side_indices {P : Type} (ps : List (P × P)) (extra : List P)
    (h : 2 ≤ ps.length) {i : Nat} (hi : i < ps.length) :
    (orderedSlots ps extra)[i]? = some (ps[i]).1 ∧
    (orderedSlots ps extra)[ps.length+i]? = some (ps[i]).2 := by
  have form : orderedSlots ps extra = ps.map Prod.fst ++ (ps.map Prod.snd ++ extra) :=
    (orderedSlots_of_two_or_more ps extra h).trans (List.append_assoc _ _ _)
  rw [form]
  constructor
  · rw [List.getElem?_append_left (by simpa using hi),List.getElem?_map,List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getElem?_append_right (by simp)]
    have e : ps.length+i-(ps.map Prod.fst).length=i := by simp
    rw [e,List.getElem?_append_left (by simpa using hi),List.getElem?_map,List.getElem?_eq_getElem hi]
    rfl

theorem each_actual_pair_separated {P : Type} (ps : List (P × P)) (extra : List P)
    (h : 2 ≤ ps.length) {i : Nat} (hi : i < ps.length) :
    let L := orderedSlots ps extra
    L[i]? = some (ps[i]).1 ∧ L[ps.length+i]? = some (ps[i]).2 ∧
       separated L.length i (ps.length+i) := by
  dsimp only
  rw [orderedSlots_size]
  refine ⟨(actual_two_side_indices ps extra h hi).1,(actual_two_side_indices ps extra h hi).2,?_⟩
  exact balanced_pairs_nonadjacent _ _ _ h hi

theorem actual_spare_pair_separated {P : Type} (a b u v : P) (rest : List P) :
    let L := orderedSlots [(a,b)] (u::v::rest)
    L[0]? = some a ∧ L[2]? = some b ∧ separated L.length 0 2 := by
  dsimp only
  rw [orderedSlots_size]
  exact ⟨rfl,rfl,one_pair_nonadjacent _ (by simp)⟩

#print axioms orderedSlots_of_two_or_more
#print axioms actual_two_side_indices
#print axioms each_actual_pair_separated
#print axioms actual_spare_pair_separated
end F5R61
