import F5R61CycleUniqueness

namespace F5R61
set_option autoImplicit false

theorem actual_pair_has_separated_indices {P : Type} (pairs : List (P × P))
    (extra : List P) (p q : P) (m : (p,q) ∈ pairs)
    (enough : 4 ≤ (orderedSlots pairs extra).length) :
    let L := orderedSlots pairs extra
    ∃ i j, L[i]? = some p ∧ L[j]? = some q ∧ separated L.length i j := by
  cases pairs with
  | nil => simp at m
  | cons a tail =>
    cases tail with
    | nil =>
      have e : a = (p,q) := by simpa using (List.mem_singleton.mp m).symm
      subst a
      have long : 2 ≤ extra.length := by
        rw [orderedSlots_size] at enough
        simp only [List.length_singleton] at enough
        omega
      cases extra with
      | nil => simp at long
      | cons u rest =>
        cases rest with
        | nil => simp at long
        | cons v others => exact ⟨0,2,actual_spare_pair_separated p q u v others⟩
    | cons b rest =>
      obtain ⟨i,hi,hr⟩ := List.mem_iff_getElem.mp m
      have long : 2 ≤ (a::b::rest).length := by simp
      have ans := each_actual_pair_separated (a::b::rest) extra long hi
      dsimp only at ans ⊢
      rw [hr] at ans
      exact ⟨i,(a::b::rest).length+i,ans⟩

theorem actual_pair_never_neighbours {P : Type} (pairs : List (P × P))
    (extra : List P) (p q : P) (m : (p,q) ∈ pairs)
    (enough : 4 ≤ (orderedSlots pairs extra).length)
    (once : (orderedSlots pairs extra).Nodup) (i j : Nat)
    (a : (orderedSlots pairs extra)[i]? = some p)
    (b : (orderedSlots pairs extra)[j]? = some q) :
    separated (orderedSlots pairs extra).length i j := by
  obtain ⟨x,y,hx,hy,h⟩ := actual_pair_has_separated_indices pairs extra p q m enough
  obtain ⟨fitX,_⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨fitY,_⟩ := List.getElem?_eq_some_iff.mp hy
  have ex := List.getElem?_inj fitX once (hx.trans a.symm)
  have ey := List.getElem?_inj fitY once (hy.trans b.symm)
  simpa [ex,ey] using h

#print axioms actual_pair_has_separated_indices
#print axioms actual_pair_never_neighbours
end F5R61
