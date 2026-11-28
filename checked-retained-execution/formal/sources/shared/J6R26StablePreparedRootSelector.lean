
import J6R24LegalLayoutMode
import J6R12RepackRootReady

/-! Installing a new legitimate stable seat order in the exact printed
recursive selector changes the root seat, not the host or minimal
rounding. Descendant calls use the ordinary pinned-selector branch. -/
namespace J6R26StablePreparedRoot
open scoped Classical Polynomial
open Polynomial J6Mesh J6OrientedHost J6RecursiveOrientation P11FullPacking
open J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint J6R12Repack
open J6R24LegalLayout J6ActiveRun J1PPrinted
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000

variable {f : ℤ[X]} {ell : ℕ} {V : Type} [Fintype V]

noncomputable def stableSelectedRoot (b m l q width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (ha : a m≤width) (cap : K m*L m≤2^width) :
    Selected (physicalRootCall f ell b m l q T w).host (a m) (Fin 64) :=
  ⟨stableRootPacking m l q width T w hm hL ha cap,
    root_minimal_rounding m l q T w (fun _ _ _=>false) hm hL (Fintype.card_fin 64)⟩

noncomputable def stableSelectedAtSchedule (b m l q native width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64) (hm : m≤K m)
    (hL : 2*l=L m) (hn : native≤m) (ha : a m≤width) (cap : K m*L m≤2^width) :
    Selected (physicalRootCall f ell b m l q T w).host
      ((rootParams f ell m native).levelBits (physicalRootCall f ell b m l q T w).depth) (Fin 64) :=
  cast (congrArg (fun n=>Selected (physicalRootCall f ell b m l q T w).host n (Fin 64))
    (mesh_root_bits m native hn).symm)
    (stableSelectedRoot (f:=f) (ell:=ell) b m l q width T w hm hL ha cap)

noncomputable def stableSelector (b m l q native width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64) (hm : m≤K m)
    (hL : 2*l=L m) (hn : native≤m) (ha : a m≤width) (cap : K m*L m≤2^width) :
    Selector (rootParams f ell m native) (sourceDelta (physicalSize m native)) :=
  pinnedSelector (rootParams f ell m native) (sourceDelta (physicalSize m native)) (physicalRootCall f ell b m l q T w)
    (stableSelectedAtSchedule b m l q native width T w hm hL hn ha cap)

theorem packing_cast_slot {H : PhysicalHost f ell} {i j : ℕ} (h : i=j)
    (p : Selected H i (Fin 64)) :
    (cast (congrArg (fun n=>Selected H n (Fin 64)) h) p).packing =
      cast (congrArg (fun n=>PhysicalPacking H.network n (Fin 64)) h) p.packing := by
  subst j
  rfl

theorem exact_stable_selector_at_root (b m l q native width : ℕ)
    (T : Plant V m q) (w : Fin (a m)→Fin 64) (hm : m≤K m)
    (hL : 2*l=L m) (hn : native≤m) (ha : a m≤width) (cap : K m*L m≤2^width)
    (d : Ready (rootParams f ell m native) (sourceDelta (physicalSize m native))
      (physicalRootCall f ell b m l q T w)) :
    packing (stableSelector b m l q native width T w hm hL hn ha cap) d =
      cast (congrArg (fun n=>PhysicalPacking (physicalRootCall f ell b m l q T w).host.network n (Fin 64))
        (mesh_root_bits m native hn).symm) (stableRootPacking m l q width T w hm hL ha cap) := by
  rw [stableSelector,pinned_at_root]
  exact packing_cast_slot (mesh_root_bits m native hn).symm
    (stableSelectedRoot b m l q width T w hm hL ha cap)

#print axioms stableSelectedRoot
#print axioms stableSelector
#print axioms exact_stable_selector_at_root
end J6R26StablePreparedRoot
