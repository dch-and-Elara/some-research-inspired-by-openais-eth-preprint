import J6R12RepackRootReady
import J6R12BlueprintReach

/-! Specialization of the all-descendant construction to the literal J6
planted root, with the printed schedule/field size and the original root
layout singled out in the selector. -/
namespace J6R12Repack
open scoped Polynomial
open J6Mesh P11FullPacking J6OrientedHost J1PPrinted
open J6ActiveRun J6R11Repack J6R12Blueprint J6R11Threshold J6R10Reachable J6R11Blueprint
variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

theorem exact_j6_root_bounds (m native : ℕ)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native)) :
    RootBounds (physicalSize m native) 2 f := by
  obtain ⟨_,hCs,hu⟩ :=
    printed_size_implies_numeric_guards (physicalSize m native) 2 (by decide) hsize
  exact ⟨hfield,by decide,hCs,hu,hsize⟩

set_option maxHeartbeats 1400000 in
theorem exact_j6_root_stable (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native)) :
    Stable (physicalSize m native) 2 (physicalRootCall f ell p m l q T w) := by
  have d := exact_j6_root_ready (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  exact stable_root _ 2 _ rfl d.edgeCount d.degree d.tags (mesh_root_linear_bound m native hn)

set_option maxHeartbeats 2100000 in
/-- Any recursive call certified reachable from the actual root, not
merely a chosen abstract call of similar dimensions, is structurally
stable. If it is active, every guard used by the native factory holds. -/
theorem exact_j6_actual_reachable (p m l q native : ℕ) (T : Plant V m q)
    (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
    (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
    (hfield : f.natDegree = 4*Nat.clog 2 (physicalSize m native))
    (hsize : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native))
    (hdeg : ∀ v, T.degree v ≤ sourceDelta (physicalSize m native))
    (c : Call (PhysicalHost f ell))
    (h : NativeReach (Plan (exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn))
      (physicalRootCall f ell p m l q T w) c) :
    Stable (physicalSize m native) 2 c ∧
    ((rootParams f ell m native).cutoff < c.edges →
     Ready (rootParams f ell m native) (sourceDelta (physicalSize m native)) c) := by
  let cfg := exact_j6_root_bounds (f:=f) m native hfield hsize
  let sel := exactJ6Selector (f:=f) (ell:=ell) p m l q native T w mask hm hL hn
  have hr := exact_j6_root_stable (f:=f) (ell:=ell) p m l q native T w mask hm hL hn hfield hsize hdeg
  have hc := stable_reachable cfg sel h hr
  exact ⟨hc,getReady cfg hc⟩

#print axioms exact_j6_root_bounds
#print axioms exact_j6_root_stable
#print axioms exact_j6_actual_reachable
end J6R12Repack
