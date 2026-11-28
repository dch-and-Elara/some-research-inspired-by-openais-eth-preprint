import J6RepairedCapacity
import J6RepairedLeaf
import J6OrientedHost

/-! Joined concrete J6 host for the direct-leaf branch, using the repaired
physical packets and the original old and subdivision node descriptions. -/
namespace J6PhysicalLeafOutput
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6RepairedCentered J6OrientedHost
open J6RecursivePortCube J6RecursiveAssembly J6ZeroTransport J6NativeHeightMesh
set_option maxHeartbeats 2500000

variable {S V Mode : Type*} [LinearOrder S] [Fintype S] [Fintype V] [Fintype Mode] [DecidableEq Mode]

theorem correct_actual_leaf_root
    (m base l q : ℕ) (host : Plant V m q) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m)
    (i : Fin (m+1)) (hS : Fintype.card S=64)
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
    let run := fun β g =>
      J6ChildPlan.run group seat target source (scopes (oldScope host w) (fun _ => Bool))
        (ports (rowPort host w) (colPort host w)) (owner w (coord m))
        (fun v y => if flag (rowTable host w) (colTable w) v y then 1 else 0)
        shift (reduceBase p (J6NativeHeightDyadic.scalar m i)) moment β g (n g) (order g)
    ((((sampleDen m i : ZMod (2^p))^M m*
        (∑ β ∈ J6RecursiveMenu.menu p weights, ∏ g, run β g)).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) =
        J6NativeHeightClearing.rationalSlot
          (fun y => good (fun v => rowTable host w v (fun j => y (rowPort host w v j))))
          (fun x => good (fun v => colTable w v (fun j => x (colPort host w v j))))
          (fun j x => ((shift j).map x).getD false) (point m i) := by
  have hOwn : ∀ v j, groupOf m l mask w h hL
      (ports (rowPort host w) (colPort host w) v j) = owner w (coord m) v :=
    owner_exact host mask w h hL (coord m)
  exact (J6RootLeaves.guarded_leaf_root m base
    (J6RepairedCapacity.actual_wire_count m l w h hL hS) i
    (rowPort host w) (colPort host w)
    (rowTable host w) (colTable w)
    (groupOf m l mask w h hL) (slotPage m l mask w h hL) (shiftAt m l mask w h hL i)
    target source (owner w (coord m)) weights hweights hOwn
    (shiftAt_group m l mask w h hL i) moment H n order hSmall).1

#print axioms correct_actual_leaf_root
end J6PhysicalLeafOutput