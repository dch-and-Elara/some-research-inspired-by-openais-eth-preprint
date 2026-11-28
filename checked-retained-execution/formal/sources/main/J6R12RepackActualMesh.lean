import J6R12RepackRootReady
import J6R12RepackFallbackMesh
import J6R12BlueprintFactory

/-! The binary sample shape of the actual physical recursive factory
retains the literal root mesh parameters. In particular the designated
odd-centre fallback has exactly the previously counted table slots. -/
namespace J6R12Repack
open scoped Polynomial
open J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R11Repack J6R12Blueprint J6R10Reachable
variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

set_option maxHeartbeats 2200000 in
theorem factory_meshAt_root (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m) :
    let r := physicalRootCall f ell p m l q T w
    let S := rootParams f ell m native
    let D := sourceDelta (physicalSize m native)
    let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
    MeshAt (paddedShape (shape S D sel) (children S D sel) r) r m := by
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · change J1PPrinted.stepU (Nat.clog 2 (physicalSize m native)) 0=u m
    exact mesh_root_width m native hn
  · change J1PPrinted.stepA (Nat.clog 2 (physicalSize m native)) 0=a m
    exact mesh_root_bits m native hn

#print axioms factory_meshAt_root
end J6R12Repack
