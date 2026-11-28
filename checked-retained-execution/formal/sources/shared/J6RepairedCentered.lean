import J6RootLeaves
import J6RecursiveOrientationLocal

/-! The actual repaired J6 layout at each printed odd center.
Labels and shift are computed from the same physical slots. -/
namespace J6RepairedCentered
open P11FullPacking J6Mesh J6RecursiveOrientation J6RecursiveOrientationLocal

variable {S : Type*} [LinearOrder S]
abbrev Ports (m l : ℕ) (w : Fin (a m) → S) :=
  J6PhysicalPacking.Wire (diagonal w) m (K m) l

def coord (m : ℕ) : Fin (a m) :=
  ⟨0, by have hb := b_pos m; unfold a; omega⟩

noncomputable def wordAt (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m)
    (p : Ports m l w) :=
  physicalCell mask (oriented mask w m l h hL p) (coord m)

noncomputable def groupOf (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) :
    Sum (Ports m l w) (Ports m l w) → S :=
  Sum.elim (fun p => (wordAt m l mask w h hL p).1)
    (fun p => (wordAt m l mask w h hL p).2)

noncomputable def slotPage (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m)
    (p : Ports m l w) : Page (a m) (K m) S :=
  (oriented mask w m l h hL p).1

noncomputable def shiftAt (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (i : Fin (m+1)) :
    Ports m l w → Option (Ports m l w) :=
  shifted mask w m l h hL (index m i)

theorem shiftAt_group (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (i : Fin (m+1))
    (p q : Ports m l w) (hm : shiftAt m l mask w h hL i p = some q) :
    groupOf m l mask w h hL (.inl p) = groupOf m l mask w h hL (.inr q) := by
  have hn : index m i ≠ 0 := Nat.ne_of_gt (address_index m i).1
  exact shifted_local mask w m l h hL _ hn _ (J6RecursiveCrossing.odd_center_valuation m i).2.1 p q hm

/-- Row/column ownership is inherited from the ordered pair, not from
the parity of an ordinal used to enumerate positions within that pair. -/
theorem groupOf_cell (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) (p : Ports m l w) :
    groupOf m l mask w h hL (.inl p) =
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h p).1 (coord m)).1 ∧
    groupOf m l mask w h hL (.inr p) =
      ((J6PhysicalPacking.place (diagonal w) m (K m) l h p).1 (coord m)).2 := by
  have hp := congrFun (orientation_preserved mask w m l h hL p) (coord m)
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

#print axioms shiftAt_group
#print axioms groupOf_cell
end J6RepairedCentered