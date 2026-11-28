import J6RootReceives
import J6ChildPlan
import J6RecursiveMenu

/-! For the explicitly generated children whose edge counts permit the source's direct leaf case, run finite Boolean assignment enumeration instead of assuming the child results. -/
namespace J6RootLeaves

open scoped BigOperators
open J6RecursiveRun J6RecursiveAssembly J6RecursivePortCube
open J6ZeroTransport J6NativeHeightMesh
open J6Mesh

universe u
variable {P G KPort V W Mode : Type*}
variable [Fintype P] [DecidableEq P] [Fintype G] [DecidableEq G]
  [Fintype KPort] [DecidableEq KPort] [Fintype V] [Fintype W]
  [Fintype Mode] [DecidableEq Mode]

theorem guarded_leaf_root
    (m base : ℕ) (hW : Fintype.card P = M m) (i : Fin (m+1))
    {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → P) (right : ∀ w, col w → P)
    (A : ∀ v, (row v → Bool) → Bool)
    (B : ∀ w, (col w → Bool) → Bool)
    (group : Sum P P → G)
    (seat : P → KPort) (shift : P → Option P)
    (target source : Mode → G × KPort)
    (owner : Sum V W → G)
    (weights : Mode → ℕ) (hweights : ∀ x, 0 < weights x)
    (hOwner : ∀ v j, group (ports left right v j) = owner v)
    (hLocal : ∀ p q, shift p = some q → group (.inl p) = group (.inr q))
    (moment : ∀ g, GroupCube group g → Mode → ZMod (2^J6SourcePrecision.printed m base))
    (H : ℕ) (n : G → ℕ)
    (order : ∀ g, Fin (n g) ≃ {q : Sum P P // group q = g})
    (hSmall : ∀ g, n g ≤ H) :
    let p := J6SourcePrecision.printed m base
    let menu := J6RecursiveMenu.menu p weights
    let run := fun β g =>
      J6ChildPlan.run group seat target source (scopes row col) (ports left right)
        owner (fun v y => if flag A B v y then 1 else 0)
        shift (reduceBase p (J6NativeHeightDyadic.scalar m i)) moment β g (n g) (order g)
    let a := fun y => good (fun v => A v (fun j => y (left v j)))
    let b := fun x => good (fun w => B w (fun j => x (right w j)))
    ((((sampleDen m i : ZMod (2^p))^M m*(∑ β ∈ menu, ∏ g, run β g)).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) =
        J6NativeHeightClearing.rationalSlot a b
          (fun p x => ((shift p).map x).getD false) (point m i) ∧
    ∀ g, J6ChildPlan.allBits (n g) (fun _ => (1:ℕ)) ≤ 2^H := by
  dsimp only
  have hpos : 0 < J6SourcePrecision.printed m base := by
    have hm : 0 < M m := by unfold M; positivity
    unfold J6SourcePrecision.printed
    positivity
  constructor
  · apply J6RootReceives.root_exact_centered m base hW i left right A B group seat
      shift target source owner _ (J6RecursiveMenu.zero_in_menu _ hpos weights hweights)
      hOwner hLocal moment
    intro β _ g
    exact J6ChildPlan.run_exact group seat target source (scopes row col)
      (ports left right) owner (fun v y => if flag A B v y then 1 else 0)
      shift _ moment β g (n g) (order g)
  · intro g
    rw [J6ChildPlan.allBits_visits]
    exact Nat.pow_le_pow_right (by decide) (hSmall g)

#print axioms guarded_leaf_root
end J6RootLeaves