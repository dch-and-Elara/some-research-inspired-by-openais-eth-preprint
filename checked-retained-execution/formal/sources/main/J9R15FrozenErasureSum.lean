import J9R15FrozenErasurePhysical

/-! A fixed profile selects the identical finite tickets before or after
the order of summing row and column assignments is exchanged. -/
namespace J9R15FrozenErasureSum
open scoped BigOperators Classical

theorem equal_sweeps {E B M K : Type*} [Fintype E] [Fintype B] [Fintype M] [CommSemiring K]
    (G : E → B → K) (L : E → B → M → K) (accept : M → Prop) :
    (∑ Y : E, ∑ X : B, G Y X * ∑ α : M, if accept α then L Y X α else 0) =
      ∑ c ∈ (Finset.univ.filter (fun c : E×M => accept c.2)), ∑ X : B, G c.1 X * L c.1 X c.2 := by
  rw [Finset.sum_filter]
  let J (c : E×M) : K := if accept c.2 then ∑ X : B, G c.1 X * L c.1 X c.2 else 0
  change _ = ∑ c, J c
  rw [Fintype.sum_prod_type J]
  apply Finset.sum_congr rfl
  intro Y _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  unfold J
  by_cases h : accept α <;> simp [h]

#print axioms equal_sweeps
end J9R15FrozenErasureSum
