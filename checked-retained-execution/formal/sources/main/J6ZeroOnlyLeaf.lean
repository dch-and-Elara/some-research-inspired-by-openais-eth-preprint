import J6ChildPlan
import J6RecursiveMenu

/-! Exact runtime-interface simplification restricted to the already
verified zero probe and the explicit Boolean leaf evaluator. -/
namespace J6ZeroOnlyLeaf

open scoped BigOperators
open J6ChildPlan J6RecursiveAssembly J6RecursiveRun J6RecursiveModes

variable {R G K V P M : Type*} [CommRing R] [Fintype G] [DecidableEq G]
  [Fintype K] [DecidableEq K] [Fintype P] [DecidableEq P] [Fintype V]
  [Fintype M] [DecidableEq M]

omit [Fintype G] [DecidableEq P] in
theorem zero_evaluator_no_moment
    (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (g : G)
    (n : ℕ) (order : Fin n ≃ {p : Sum P P // group p = g}) :
    run group seat target source scope port owner table shift c moment 0 g n order =
    run group seat target source scope port owner table shift c (fun _ _ _ => 0) 0 g n order := by
  unfold run packetAtZero
  simp only [Finsupp.filter_zero, if_true, Finsupp.zero_apply, pow_zero,
    Finset.prod_const_one, mul_one]

theorem leaf_evaluator_zero_only
    (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R)
    (n : G → ℕ) (order : ∀ g, Fin (n g) ≃ {p : Sum P P // group p = g})
    (p : ℕ) (hp : 0 < p) (weights : M → ℕ) (hw : ∀ x, 0 < weights x) :
    (∑ β ∈ J6RecursiveMenu.menu p weights, ∏ g,
      run group seat target source scope port owner table shift c moment β g (n g) (order g)) =
    ∏ g, run group seat target source scope port owner table shift c
      (fun _ _ _ => 0) 0 g (n g) (order g) := by
  classical
  rw [Finset.sum_eq_single_of_mem 0 (J6RecursiveMenu.zero_in_menu p hp weights hw)]
  · exact Finset.prod_congr rfl
      (fun g _ => zero_evaluator_no_moment group seat target source scope port owner table
        shift c moment g (n g) (order g))
  · intro β _ hb
    simp only [run_exact]
    unfold rootChild
    exact offZero_childProduct target source (addresses group seat)
      (retained group scope port owner table) _ _ moment β hb

omit [DecidableEq G] in
theorem zero_leaf_assignments (n : G → ℕ) (H : ℕ) (small : ∀ g, n g ≤ H) :
    (∑ g, allBits (n g) (fun _ => (1 : ℕ))) ≤ Fintype.card G * 2^H := by
  calc
    _ ≤ ∑ _g : G, (2^H : ℕ) := by
      apply Finset.sum_le_sum
      intro g _
      rw [allBits_visits]
      exact Nat.pow_le_pow_right (by decide) (small g)
    _ = _ := by simp

#print axioms zero_evaluator_no_moment
#print axioms leaf_evaluator_zero_only
#print axioms zero_leaf_assignments
end J6ZeroOnlyLeaf