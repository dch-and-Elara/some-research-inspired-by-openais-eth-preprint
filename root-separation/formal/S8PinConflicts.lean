import S8Conflicts

namespace S8

open scoped BigOperators

variable {V W G J : Type*} [Fintype V] [Fintype W] [Fintype J] [DecidableEq J]

noncomputable def ownerFiber (owner : V ≃ G × J) (g : G) : J ↪ V :=
  ⟨fun j => owner.symm (g,j), fun _ _ h => congrArg Prod.snd (owner.symm.injective h)⟩

noncomputable def pinNeighbors (pin : V ↪ W) (owner : V ≃ G × J) (e : W) : Finset W := by
  classical
  exact if he : ∃ v, pin v = e then
    let r := owner (Classical.choose he)
    (Finset.univ.erase r.2).map ((ownerFiber owner r.1).trans pin)
  else ∅

omit [Fintype W] in
theorem pinNeighbors_at (pin : V ↪ W) (owner : V ≃ G × J) (v : V) :
    pinNeighbors pin owner (pin v) =
      (Finset.univ.erase (owner v).2).map ((ownerFiber owner (owner v).1).trans pin) := by
  classical
  let he : ∃ u, pin u = pin v := ⟨v,rfl⟩
  have h : Classical.choose he = v := pin.injective (Classical.choose_spec he)
  simp only [pinNeighbors, dif_pos he, h]

theorem pinNeighbors_mem (pin : V ↪ W) (owner : V ≃ G × J) (v w : V)
    (sameGroup : (owner v).1 = (owner w).1) (distinct : v ≠ w) :
    pin w ∈ pinNeighbors pin owner (pin v) := by
  rw [pinNeighbors_at]
  refine Finset.mem_map.mpr ⟨(owner w).2, Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩, ?_⟩
  · intro h
    exact distinct (owner.injective (Prod.ext sameGroup h.symm))
  · simp [ownerFiber, sameGroup]

theorem pinNeighbors_sum (pin : V ↪ W) (owner : V ≃ G × J) :
    ∑ e, (pinNeighbors pin owner e).card = Fintype.card V * (Fintype.card J - 1) := by
  classical
  have h : ∑ e ∈ (Finset.univ.map pin), (pinNeighbors pin owner e).card =
      ∑ e, (pinNeighbors pin owner e).card := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hn : ¬∃ v, pin v = e := by
      simpa only [Finset.mem_map, Finset.mem_univ, true_and] using he
    simp [pinNeighbors, hn]
  rw [← h, Finset.sum_map]
  simp only [pinNeighbors_at, Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

#print axioms pinNeighbors_mem
#print axioms pinNeighbors_sum

end S8

