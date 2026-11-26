import J6RecursiveAssembly
import J6RecursiveCrossing
import Mathlib.Tactic

/-! Finite Appendix D zero-mode root register evaluated by recursive
children. The precise remaining implementation premise is correctness
of the supplied child results for the source-generated finite child
tensors. This module does not assume the full parent contraction. -/
namespace J6RecursiveRun
open scoped BigOperators
open J6RecursiveAssembly J6RecursiveModes J6RecursiveCrossing
open J6PhysicalPacking J6NativeHeightPort J6Mesh

variable {R G K V P M : Type*} [CommRing R] [Fintype G] [DecidableEq G]
  [Fintype K] [DecidableEq K] [Fintype P] [DecidableEq P] [Fintype V]
  [Fintype M] [DecidableEq M]

noncomputable def rootChild (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (β : M →₀ ℕ) (g : G) : R :=
  child target source (addresses group seat) (retained group scope port owner table)
    (fun g y p => extend group g y (.inl p))
    (fun g y p => value c (read shift (extend group g y) p))
    (fun _ _ _ _ => 0) moment β g

theorem exact_parent_of_child_results (group : Sum P P → G) (seat : P → K)
    (target source : M → G × K) (scope : V → Type*)
    (port : ∀ v, scope v → Sum P P) (owner : V → G)
    (table : ∀ v, (scope v → Bool) → R) (shift : P → Option P) (c : R)
    (moment : ∀ g, GroupCube group g → M → R) (menu : Finset (M →₀ ℕ)) (hzero : 0 ∈ menu)
    (hOwner : ∀ v j, group (port v j)=owner v)
    (hLocal : ∀ p q, shift p=some q → group (.inl p)=group (.inr q))
    (run : (M →₀ ℕ) → G → R)
    (correct : ∀ β ∈ menu, ∀ g,
      run β g = rootChild group seat target source scope port owner table shift c moment β g) :
    (∑ β ∈ menu, ∏ g, run β g) = wholeContraction scope port table shift c := by
  classical
  calc
    _ = ∑ β ∈ menu, ∏ g, rootChild group seat target source scope port owner table shift c moment β g :=
      Finset.sum_congr rfl (fun β hβ => Finset.prod_congr rfl (fun g _ => correct β hβ g))
    _ = _ := by
      unfold rootChild
      rw [exact_zero_mode_register _ _ _ _ _ _ _ _ hzero]
      exact physical_child_assembly _ _ _ _ _ _ _ _ hOwner hLocal

section Physical
variable {C : Type*} [Fintype C] [DecidableEq C]
def packedGroup (first second : C → G) (rho : C) (m l : ℕ) (h : m ≤ J6Mesh.K m) :
    Sum (Wire rho m (J6Mesh.K m) l) (Wire rho m (J6Mesh.K m) l) → G :=
  Sum.elim
    (fun p => let s := place rho m (J6Mesh.K m) l h p
              rowLabel (first s.1) (second s.1) s.2.2.val)
    (fun p => let s := place rho m (J6Mesh.K m) l h p
              colLabel (first s.1) (second s.1) s.2.2.val)

omit [Fintype G] [DecidableEq G] [Fintype C] in
theorem packed_group_local (first second : C → G) (rho : C) (m l : ℕ) (h : m ≤ J6Mesh.K m)
    (i : Fin (m+1)) (p q : Wire rho m (J6Mesh.K m) l)
    (hq : shiftedWire rho m (J6Mesh.K m) l h (index m i) p = some q) :
    packedGroup first second rho m l h (.inl p) =
      packedGroup first second rho m l h (.inr q) :=
  packed_shift_local first second rho m l h i p q hq
end Physical

#print axioms exact_parent_of_child_results
#print axioms packed_group_local
end J6RecursiveRun
