import J6SourceMoment

namespace J6ChildGroup
open scoped BigOperators Classical
open J6BlockFactor
variable {R M K G : Type*} [CommRing R] [Fintype M] [Fintype K] [Fintype G]
variable {Val : G → Type*} [∀ g, Fintype (Val g)]

/-- Sum over one shared assignment per group. Each target block and each
source moment sees only its own group's assignment. Old entries are already
multiplied per group, before summing; they are not separated by packet. -/
theorem contract_grouped (atTarget : K → G) (atSource : M → G)
    (old : ∀ g, Val g → R)
    (coeff : ∀ k, Val (atTarget k) → R)
    (moment : ∀ m, Val (atSource m) → R) :
    (∑ x : ∀ g, Val g,
      (∏ g, old g (x g)) * (∏ m, moment m (x (atSource m))) *
      (∏ k, coeff k (x (atTarget k)))) =
      ∏ g, ∑ y : Val g, old g y *
        (∏ m : rows atSource g, moment m.val (m.property.symm ▸ y)) *
        (∏ k : rows atTarget g, coeff k.val (k.property.symm ▸ y)) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_rows atSource (fun m => moment m (x (atSource m))),
    prod_rows atTarget (fun k => coeff k (x (atTarget k))),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  have hm : (∏ m : rows atSource g, moment m.val (x (atSource m.val))) =
      ∏ m : rows atSource g, moment m.val (m.property.symm ▸ x g) := by
    apply Finset.prod_congr rfl
    intro m _
    rcases m with ⟨m, hm⟩
    change atSource m = g at hm
    subst g
    rfl
  have hk : (∏ k : rows atTarget g, coeff k.val (x (atTarget k.val))) =
      ∏ k : rows atTarget g, coeff k.val (k.property.symm ▸ x g) := by
    apply Finset.prod_congr rfl
    intro k _
    rcases k with ⟨k, hk⟩
    change atTarget k = g at hk
    subst g
    rfl
  rw [hm, hk]

#print axioms contract_grouped
end J6ChildGroup
