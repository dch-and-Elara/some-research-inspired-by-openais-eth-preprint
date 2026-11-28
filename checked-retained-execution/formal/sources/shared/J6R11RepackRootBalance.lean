import J6R11RepackRootChart
import J6R10RepackState
import J6R9ZeroBalance

/-! With the actual root graph installed in the reusable repacker, the
previous fully-padded J6 balance theorem computes its next call sizes.
These are statement-level cardinalities, not assumptions from a leaf model. -/
namespace J6R11Repack
open scoped Classical
open P11FullPacking J6Mesh J6OrientedHost J6RepairedCentered J6R10Repack
variable {S V : Type*} [LinearOrder S] [Fintype S]

theorem root_group_raw (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (p : Port (Ports m l w)) :
    retainedGroup (rootNetwork T w) (atGroup (rootPacking m l q T w mask h hL hS) (coord m)) p =
      groupOf m l mask w h hL p := by
  cases p with
  | inl e => exact (row_symbol (rootPacking m l q T w mask h hL hS) (coord m) e).symm
  | inr e => exact (col_symbol (rootPacking m l q T w mask h hL hS) (coord m) e).symm

theorem actual_repacked_root_group_size (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (g : S) :
    let P := rootPacking m l q T w mask h hL hS
    32 * Nat.card (ChildEdge (rootNetwork T w) (atGroup P (coord m)) g) = M m := by
  dsimp only
  let P := rootPacking m l q T w mask h hL hS
  have he : ChildEdge (rootNetwork T w) (atGroup P (coord m)) g ≃
      {p : Port (Ports m l w) // groupOf m l mask w h hL p = g} :=
    Equiv.subtypeEquivRight (fun p => by rw [root_group_raw m l q T w mask h hL hS p])
  rw [Nat.card_congr he]
  exact J6R9ZeroBalance.actual_group_card m l mask w h hL hS g

theorem actual_repacked_root_children_active (m l q native : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S) (h : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (hn : native≤m) (g : S) :
    let P := rootPacking m l q T w mask h hL hS
    J6R9ZeroCutoff.cutoff (physicalSize m native) (Nat.clog 2 (physicalSize m native)) <
      Nat.card (ChildEdge (rootNetwork T w) (atGroup P (coord m)) g) := by
  apply J6R9ZeroCutoff.actual_J6_balanced_above_cutoff m native _ hn
  exact actual_repacked_root_group_size m l q T w mask h hL hS g

#print axioms root_group_raw
#print axioms actual_repacked_root_group_size
#print axioms actual_repacked_root_children_active
end J6R11Repack
