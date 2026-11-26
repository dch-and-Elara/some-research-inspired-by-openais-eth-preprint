import J6RecursiveRun
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Appendix D, quantitative-contraction.tex lines 85, 487–508 and
566–569: direct summation at a child with no more than H edges.  Here the
child is the literal source-generated packet/retained network at the
zero sample.  The enumeration is a recursive executable Boolean fold
on a supplied exact ordering of its edges, not a supplied child answer.
The source describes the retained entries; this module does not compile
their input byte representation or the active Hermite recursion. -/
namespace J6ChildPlan
open scoped BigOperators
open J6RecursiveAssembly J6RecursiveRun

/-- Visit each Boolean vector by first fixing one edge to 0 and then 1. -/
def allBits {R : Type*} [AddCommMonoid R] :
    (n : ℕ) → ((Fin n → Bool) → R) → R
  | 0, f => f Fin.elim0
  | n+1, f => allBits n (fun a => f (Fin.cons false a)) +
      allBits n (fun a => f (Fin.cons true a))

theorem allBits_exact {R : Type*} [AddCommMonoid R] (n : ℕ) (f : (Fin n → Bool) → R) :
    allBits n f = ∑ x, f x := by
  induction n with
  | zero =>
    change f Fin.elim0 = _
    exact (Finset.sum_eq_single (f := f) Fin.elim0
      (fun x _ hx => (hx (Subsingleton.elim _ _)).elim)
      (fun h => (h (Finset.mem_univ _)).elim)).symm
  | succ n ih =>
    simp only [allBits, ih]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) f]
    rw [Fintype.sum_prod_type]
    simp [Fin.consEquiv]
    exact add_comm _ _

/-- No part of leaf work is hidden in a call returning the whole sum. -/
theorem allBits_visits (n : ℕ) : allBits n (fun _ => (1 : ℕ)) = 2 ^ n := by
  rw [allBits_exact]
  simp

variable {R G K V P M : Type*} [CommRing R] [Fintype G] [DecidableEq G]
  [Fintype K] [DecidableEq K] [Fintype P] [DecidableEq P] [Fintype V]
  [Fintype M] [DecidableEq M]

/-- At the zero sample the packet polynomial is constant.  Target
exponents give an explicit zero test; source-only exponents retain
their powers even in a packet with no target row. -/
def packetAtZero (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R)
    (moment : M → R) (β : M →₀ ℕ) : R :=
  if β.filter (fun m => target m = (g,k)) = 0 then
    (∏ p ∈ ports, LiteralPortCompiler.affine (bit p) (base p)) *
      ∏ m ∈ Finset.univ.filter (fun m => source m = (g,k)), moment m ^ β m
  else 0

omit [Fintype G] [Fintype K] [Fintype P] [DecidableEq P] [Fintype V] in
theorem packetAtZero_exact (target source : M → G × K) (g : G) (k : K)
    (ports : Finset P) (bit : P → Bool) (base : P → R) (moment : M → R) (β : M →₀ ℕ) :
    packetAtZero target source g k ports bit base moment β =
      J6RecursiveModes.packet target source g k ports bit base (fun _ _ => 0) moment β := by
  classical
  by_cases h : β.filter (fun m => target m = (g,k)) = 0
  · simp [packetAtZero, J6RecursiveModes.packet, J6RecursiveModes.row_zero,
      ← map_prod, MvPolynomial.coeff_C, h]
  · simp [packetAtZero, J6RecursiveModes.packet, J6RecursiveModes.row_zero,
      ← map_prod, MvPolynomial.coeff_C, h, Ne.symm h]

def orderBits (group : Sum P P → G) (g : G) (n : ℕ)
    (order : Fin n ≃ {p : Sum P P // group p = g}) :
    (Fin n → Bool) ≃ GroupCube group g := order.arrowCongr (Equiv.refl Bool)

/-- The actual leaf direct recipe, reading only individual retained
tensor entries and building each packet entry from its defining factors. -/
def run (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (β : M →₀ ℕ) (g : G)
    (n : ℕ) (order : Fin n ≃ {p : Sum P P // group p = g}) : R :=
  allBits n fun bits =>
    let y := orderBits group g n order bits
    (∏ v ∈ Finset.univ.filter (fun v => owner v = g),
      table v (fun j => extend group g y (port v j))) *
      ∏ k, packetAtZero target source g k (addresses group seat g k)
        (fun p => extend group g y (.inl p))
        (fun p => value c (read shift (extend group g y) p)) (moment g y) β

omit [Fintype G] in
theorem run_exact (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (β : M →₀ ℕ) (g : G)
    (n : ℕ) (order : Fin n ≃ {p : Sum P P // group p = g}) :
    run group seat target source scope port owner table shift c moment β g n order =
      rootChild group seat target source scope port owner table shift c moment β g := by
  unfold run rootChild J6RecursiveModes.child
  rw [allBits_exact]
  apply Fintype.sum_equiv (orderBits group g n order)
  intro a
  dsimp only
  simp only [retained, packetAtZero_exact]

/-- When the generated children are all below the printed leaf cutoff,
their exhibited finite computations supply the root identity without a
"correct child results" premise. The second component counts assignments,
not entry-generation bit cost. -/
theorem parent_with_direct_leaves (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (menu : Finset (M →₀ ℕ)) (hzero : 0 ∈ menu)
    (hOwner : ∀ v j, group (port v j) = owner v)
    (hLocal : ∀ p q, shift p = some q → group (.inl p) = group (.inr q))
    (H : ℕ) (n : G → ℕ) (order : ∀ g, Fin (n g) ≃ {p : Sum P P // group p = g})
    (hSmall : ∀ g, n g ≤ H) :
    (∑ β ∈ menu, ∏ g, run group seat target source scope port owner table shift c moment β g
      (n g) (order g)) = wholeContraction scope port table shift c ∧
      ∀ g, allBits (n g) (fun _ => (1 : ℕ)) ≤ 2 ^ H := by
  constructor
  · apply exact_parent_of_child_results group seat target source scope port owner table shift c
      moment menu hzero hOwner hLocal
    intro β _ g
    exact run_exact group seat target source scope port owner table shift c moment β g (n g) (order g)
  · intro g
    rw [allBits_visits]
    exact Nat.pow_le_pow_right (by decide) (hSmall g)

example : allBits 3 (fun w => if w 0 && w 1 then (2 : ℤ) else 0) = 4 := by
  decide

#print axioms allBits_exact
#print axioms allBits_visits
#print axioms packetAtZero_exact
#print axioms run_exact
#print axioms parent_with_direct_leaves
end J6ChildPlan