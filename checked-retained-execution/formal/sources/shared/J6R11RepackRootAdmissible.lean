import J6R11RepackRootChart
import J6R10RepackRounded

/-! The special J6 planting uses the exact minimum packet rounding of an
admissible complete labelling. This does not assert that an independently
tie-broken naming heuristic must choose the same layout. -/
namespace J6R11Repack
open scoped Classical
open P11FullPacking J6OrientedHost J6RecursiveOrientation J6Mesh J6R10Repack
variable {S V : Type*} [LinearOrder S] [Fintype S]

private def firstFiber {X Y : Type*} (c : X) : {z : X×Y // z.1=c} ≃ Y where
  toFun z := z.val.2
  invFun y := ⟨(c,y),rfl⟩
  left_inv z := Subtype.ext (Prod.ext z.property.symm rfl)
  right_inv _ := rfl

set_option maxHeartbeats 1100000 in
theorem root_exact_cell_load (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (c : Cell (Fin (a m)) S) :
    let P := rootPacking m l q T w mask h hL hS
    Nat.card (RealFiber (declaredCell (rootNetwork T w) P.rowLabel P.colLabel) c) = K m * L m := by
  dsimp only
  let P := rootPacking m l q T w mask h hL hS
  let move := (Equiv.ofBijective (oriented mask w m l h hL)
    ⟨orientation_injective mask w m l h hL,orientation_surjective mask w m l h hL⟩).trans
      (fullSlotChart mask)
  have he (e : Wire w m (K m) l) :
      (move e).1 = declaredCell (rootNetwork T w) P.rowLabel P.colLabel e :=
    (fullSlotChart_cell mask _).trans (P.exactCell e)
  have hCard := Nat.card_congr ((Equiv.subtypeEquiv (p :=
    fun e : Wire w m (K m) l => declaredCell (rootNetwork T w) P.rowLabel P.colLabel e = c)
    (q := fun e => e.1 = c) move (fun e => by
      change declaredCell (rootNetwork T w) P.rowLabel P.colLabel e = c ↔ (move e).1 = c
      rw [he e])).trans (firstFiber c))
  simpa only [Nat.card_fin] using hCard

set_option maxHeartbeats 1000000 in
theorem root_minimal_rounding (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64) :
    let P := rootPacking m l q T w mask h hL hS
    P.copies = ceilCopies (L m) (maxFiber (declaredCell (rootNetwork T w) P.rowLabel P.colLabel)) := by
  dsimp only
  let P := rootPacking m l q T w mask h hL hS
  let labels := declaredCell (rootNetwork T w) P.rowLabel P.colLabel
  letI : Nonempty (Cell (Fin (a m)) S) := ⟨diagonal w⟩
  obtain ⟨c,hc⟩ := attained_max labels
  change K m = ceilCopies (L m) (maxFiber labels)
  rw [← hc, root_exact_cell_load m l q T w mask h hL hS c]
  unfold ceilCopies
  rw [Nat.mul_div_cancel _ (show 0 < L m by unfold L; positivity)]
  simp

#print axioms root_exact_cell_load
#print axioms root_minimal_rounding
end J6R11Repack
