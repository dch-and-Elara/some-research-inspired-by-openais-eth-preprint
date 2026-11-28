import J6R12RepackRootChoice
import J6R12BlueprintSite

/-! Exact layout selector for the native mode and child factories. One
selector controls both; they cannot independently choose another
admissible but different mesh after a mode index has already been read. -/
namespace J6R12Repack
open scoped Classical Polynomial
open P11FullPacking J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
open J6ActiveRun J6OrientedHost J6Mesh
variable {f : ℤ[X]} {ell : ℕ}

noncomputable def pinnedSelector (P : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (special : Selected root.host (P.levelBits root.depth) (Fin 64)) :
    Selector P Δ :=
  fun c d => (select root P.levelBits Δ (Fintype.card_fin 64) special c
    (fun _ => guards_for_call c _ Δ d.edgeCount d.degree d.collision d.paddedSlots)).packing

theorem pinned_at_root (P : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (special : Selected root.host (P.levelBits root.depth) (Fin 64))
    (d : Ready P Δ root) :
    packing (pinnedSelector P Δ root special) d = special.packing := by
  unfold packing pinnedSelector
  rw [select_root]

theorem pinned_at_nonroot (P : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (special : Selected root.host (P.levelBits root.depth) (Fin 64))
    (c : Call (PhysicalHost f ell)) (d : Ready P Δ c) (different : c≠root) :
    packing (pinnedSelector P Δ root special) d =
      (fresh c.host (P.levelBits c.depth) Δ (Fintype.card_fin 64)
        (guards_for_call c _ Δ d.edgeCount d.degree d.collision d.paddedSlots)).packing := by
  unfold packing pinnedSelector
  rw [select_other _ _ _ _ _ _ _ different]

theorem pinned_minimal (P : Params (f:=f) (ell:=ell)) (Δ : ℕ)
    (root : Call (PhysicalHost f ell))
    (special : Selected root.host (P.levelBits root.depth) (Fin 64))
    (c : Call (PhysicalHost f ell)) (d : Ready P Δ c) :
    let g := packing (pinnedSelector P Δ root special) d
    g.copies =
      ceilCopies (2^P.levelBits c.depth) (maxFiber (declaredCell c.host.network g.rowLabel g.colLabel)) :=
  (select root P.levelBits Δ (Fintype.card_fin 64) special c
    (fun _ => guards_for_call c _ Δ d.edgeCount d.degree d.collision d.paddedSlots)).minimal

variable {V : Type} [Fintype V]

/-- Same pinned selector, specialized to the concrete J6 planting and the
original paired subdivision gates. The sole bit-width equality is an
exact printed schedule fact, not chosen arbitrary geometry. -/
noncomputable def actualJ6Selector (P : Params (f:=f) (ell:=ell)) (Δ p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → Fin 64)
    (mask : MaskFamily (a m) (K m) (Fin 64)) (hm : m≤K m) (hL : 2*l=L m)
    (hbits : P.levelBits 0=a m) : Selector P Δ :=
  pinnedSelector P Δ (physicalRootCall f ell p m l q T w)
    (actualSelectedAtSchedule f ell p m l q T w mask hm hL (Fintype.card_fin 64) P.levelBits hbits)

theorem actual_j6_root_pinned (P : Params (f:=f) (ell:=ell)) (Δ p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → Fin 64)
    (mask : MaskFamily (a m) (K m) (Fin 64)) (hm : m≤K m) (hL : 2*l=L m)
    (hbits : P.levelBits 0=a m)
    (d : Ready P Δ (physicalRootCall f ell p m l q T w)) :
    packing (actualJ6Selector P Δ p m l q T w mask hm hL hbits) d =
      (actualSelectedAtSchedule f ell p m l q T w mask hm hL (Fintype.card_fin 64) P.levelBits hbits).packing :=
  pinned_at_root P Δ _ _ d

#print axioms pinnedSelector
#print axioms pinned_at_root
#print axioms pinned_at_nonroot
#print axioms pinned_minimal
#print axioms actual_j6_root_pinned
end J6R12Repack
