import J6RepairedCentered
import J6ChildPlan
import J6RecursivePortCube
import J6ZeroTransport

/-! The repaired visible packing, returned leaf computation, and centered
decoder use the same port numbering. No equality with the old capacity chart's
padding residue is intended. -/
namespace J6RepairedLeaf
open scoped BigOperators Classical
set_option maxHeartbeats 1100000
open P11FullPacking J6Mesh J6RepairedCentered
open J6RecursiveOrientation J6RecursiveAssembly J6RecursivePortCube
open J6ZeroTransport J6NativeHeightMesh
universe u

variable {S V W Mode : Type*} [LinearOrder S] [Fintype S]
variable [Fintype V] [Fintype W] [Fintype Mode] [DecidableEq Mode]

omit [Fintype S] [Fintype V] [Fintype W] in
theorem owner_from_labels
    (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m)
    {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → Ports m l w) (right : ∀ v, col v → Ports m l w)
    (leftWord : V → Fin (a m) → S) (rightWord : W → Fin (a m) → S)
    (labL : ∀ v j i,
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h (left v j)).1 i).1 = leftWord v i)
    (labR : ∀ v j i,
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h (right v j)).1 i).2 = rightWord v i)
    (v : Sum V W) (j : scopes row col v) :
    groupOf m l mask w h hL (ports left right v j) =
      Sum.elim (fun v => leftWord v (coord m)) (fun v => rightWord v (coord m)) v := by
  cases v with
  | inl v =>
    exact (groupOf_cell m l mask w h hL (left v j)).1.trans (labL v j (coord m))
  | inr v =>
    exact (groupOf_cell m l mask w h hL (right v j)).2.trans (labR v j (coord m))

theorem least_repaired_node
    (m base l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (i : Fin (m+1))
    (hW : Fintype.card (Ports m l w) = M m)
    {row : V → Type u} {col : W → Type u}
    (left : ∀ v, row v → Ports m l w) (right : ∀ v, col v → Ports m l w)
    (A : ∀ v, (row v → Bool) → Bool) (B : ∀ v, (col v → Bool) → Bool)
    (leftWord : V → Fin (a m) → S) (rightWord : W → Fin (a m) → S)
    (labL : ∀ v j i,
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h (left v j)).1 i).1 = leftWord v i)
    (labR : ∀ v j i,
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h (right v j)).1 i).2 = rightWord v i)
    (target source : Mode → S × Page (a m) (K m) S)
    (weights : Mode → ℕ) (hweights : ∀ k, 0 < weights k)
    (moment : ∀ g, GroupCube (groupOf m l mask w h hL) g → Mode → ZMod (2^J6SourcePrecision.printed m base))
    (H : ℕ) (n : S → ℕ)
    (order : ∀ g, Fin (n g) ≃ {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g})
    (hSmall : ∀ g, n g ≤ H) :
    let p := J6SourcePrecision.printed m base
    let shift := shiftAt m l mask w h hL i
    let group := groupOf m l mask w h hL
    let seat := slotPage m l mask w h hL
    let owner := Sum.elim (fun v => leftWord v (coord m)) (fun v => rightWord v (coord m))
    let run := fun β g =>
      J6ChildPlan.run group seat target source (scopes row col) (ports left right) owner
        (fun v y => if flag A B v y then 1 else 0)
        shift (reduceBase p (J6NativeHeightDyadic.scalar m i)) moment β g (n g) (order g)
    ((((sampleDen m i : ZMod (2^p))^M m*
        (∑ β ∈ J6RecursiveMenu.menu p weights, ∏ g, run β g)).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) =
        J6NativeHeightClearing.rationalSlot
          (fun y => good (fun v => A v (fun j => y (left v j))))
          (fun x => good (fun v => B v (fun j => x (right v j))))
          (fun j x => ((shift j).map x).getD false) (point m i) ∧
    ∀ g, J6ChildPlan.allBits (n g) (fun _ => (1:ℕ)) ≤ 2^H := by
  exact J6RootLeaves.guarded_leaf_root m base hW i left right A B
    (groupOf m l mask w h hL) (slotPage m l mask w h hL)
    (shiftAt m l mask w h hL i) target source _ weights hweights
    (owner_from_labels m l mask w h hL left right leftWord rightWord labL labR)
    (shiftAt_group m l mask w h hL i) moment H n order hSmall

#print axioms owner_from_labels
#print axioms least_repaired_node
end J6RepairedLeaf