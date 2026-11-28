import J6RecursiveRun
import J6RecursivePortCube
import J6ZeroTransportSource

/-! J6 receives the explicitly specified root sum over the Appendix D
child values. This proof is independent of the choice of physical chart;
it still requires correct execution of the specified child contractions,
and does not manufacture ownership or same-group hypotheses. -/
namespace J6RootReceives

open scoped BigOperators
open J6RecursiveRun J6RecursiveAssembly J6RecursivePortCube
open J6ZeroTransport J6NativeHeightMesh
open J6Mesh

universe u
variable {P G KPort V W Mode : Type*}
variable [Fintype P] [DecidableEq P] [Fintype G] [DecidableEq G]
  [Fintype KPort] [DecidableEq KPort] [Fintype V] [Fintype W]
  [Fintype Mode] [DecidableEq Mode]

theorem root_exact_centered
    (m base : ℕ) (hW : Fintype.card P = M m) (i : Fin (m+1))
    {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → P) (right : ∀ w, col w → P)
    (A : ∀ v, (row v → Bool) → Bool)
    (B : ∀ w, (col w → Bool) → Bool)
    (group : Sum P P → G)
    (seat : P → KPort) (shift : P → Option P)
    (target source : Mode → G × KPort)
    (owner : Sum V W → G)
    (menu : Finset (Mode →₀ ℕ)) (hzero : 0 ∈ menu)
    (hOwner : ∀ v j, group (ports left right v j) = owner v)
    (hLocal : ∀ p q, shift p = some q → group (.inl p) = group (.inr q))
    (moment : ∀ g, GroupCube group g → Mode → ZMod (2^J6SourcePrecision.printed m base))
    (run : (Mode →₀ ℕ) → G → ZMod (2^J6SourcePrecision.printed m base))
    (correct : ∀ β ∈ menu, ∀ g,
      run β g = rootChild group seat target source (scopes row col) (ports left right)
        owner (fun v y => if flag A B v y then 1 else 0)
        shift (reduceBase (J6SourcePrecision.printed m base) (J6NativeHeightDyadic.scalar m i)) moment β g) :
    let p := J6SourcePrecision.printed m base
    let a := fun y => good (fun v => A v (fun j => y (left v j)))
    let b := fun x => good (fun w => B w (fun j => x (right w j)))
    ((((sampleDen m i : ZMod (2^p))^M m*(∑ β ∈ menu, ∏ g, run β g)).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) =
        J6NativeHeightClearing.rationalSlot a b
          (fun p x => ((shift p).map x).getD false) (point m i) := by
  dsimp only
  apply J6NativeHeightLift.exact_centered_readout m base i hW _ _ _
    (reduceBase (J6SourcePrecision.printed m base))
  rw [exact_parent_of_child_results group seat target source (scopes row col)
    (ports left right) owner (fun v y => if flag A B v y then 1 else 0) _
    _ moment menu hzero hOwner hLocal run correct]
  exact whole_eq_residueSlot left right A B shift _

#print axioms root_exact_centered
end J6RootReceives