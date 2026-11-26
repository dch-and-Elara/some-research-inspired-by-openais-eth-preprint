import J6ChildIdentity

namespace J6PhysicalAssignment
open scoped BigOperators Classical
open J6BlockFactor

variable {P G R : Type*} [Fintype P] [Fintype G] [AddCommMonoid R]
variable {B : P → Type*} [∀ i, Fintype (B i)]

/-- Each physical incidence bit appears in one group. No copying, resampling
 or separation of bits within a group is used in the change of index. -/
def restrictEquiv (group : P → G) : (∀ i, B i) ≃ (∀ g, ∀ i : rows group g, B i.val) where
  toFun x _ i := x i.val
  invFun y i := y (group i) ⟨i,rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext g i
    rcases i with ⟨i, e⟩
    change group i = g at e
    subst g
    rfl

omit [AddCommMonoid R] [Fintype P] [Fintype G] [∀ i, Fintype (B i)] in
theorem read_restriction (group : P → G) (x : ∀ i, B i) (i : P) :
    (restrictEquiv group x) (group i) ⟨i,rfl⟩ = x i := rfl

theorem sum_over_physical_assignments (group : P → G)
    (f : (∀ g, ∀ i : rows group g, B i.val) → R) :
    (∑ x : ∀ i, B i, f (restrictEquiv group x)) = ∑ y, f y := by
  classical
  exact Fintype.sum_equiv (restrictEquiv group) _ _ (fun _ => rfl)

#print axioms read_restriction
#print axioms sum_over_physical_assignments
end J6PhysicalAssignment
