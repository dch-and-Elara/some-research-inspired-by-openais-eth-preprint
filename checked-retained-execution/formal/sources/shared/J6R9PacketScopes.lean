import J6R9PacketTiles
import P11FullPackingPlacement
import Mathlib.Tactic

/-! Actual printed packet/group addressing for nonzero probes.
A mode's tile word determines both endpoints. Every real column
contributing to its moment is in the mode's source group. -/
namespace J6R9PacketScopes
open P11FullPacking J6R9PacketTiles
open scoped BigOperators
variable {S : Type*} [LinearOrder S] {a b : ℕ}

def tileIndex (i : Fin a) (τ : Fin (2^(i.val+1))) : Fin (2^a) :=
  Fin.castLE (Nat.pow_le_pow_right (by decide) i.isLt) τ

def rowGroup (mask : MaskFamily a b S) (i : Fin a) (p : Physical a b S) : S :=
  (physicalCell mask p i).1

def colGroup (mask : MaskFamily a b S) (i : Fin a) (p : Physical a b S) : S :=
  (physicalCell mask p i).2

theorem cell_same_bit (mask : MaskFamily a b S) (k : Page a b S)
    (i : Fin a) (x y : Fin (2^a))
    (h : x.val.testBit i.val = y.val.testBit i.val) :
    physicalCell mask (k,x) i = physicalCell mask (k,y) i := by
  simp only [physicalCell,cell,slotOrient,shiftMask,bits,h]

theorem different_groups_same_bit (mask : MaskFamily a b S) (k : Page a b S)
    (i : Fin a) (x y : Fin (2^a))
    (h : rowGroup mask i (k,x) ≠ colGroup mask i (k,y)) :
    x.val.testBit i.val = y.val.testBit i.val := by
  by_cases h' : (k.1.val i).1 ≠ (k.1.val i).2
  · cases hm : mask k.1 k.2 ⟨i,h'⟩ <;>
      cases hx : x.val.testBit i.val <;> cases hy : y.val.testBit i.val <;>
      simp [rowGroup,colGroup,physicalCell,cell,h',slotOrient,shiftMask,bits,hm,hx,hy] at h ⊢
  · have he : (k.1.val i).1=(k.1.val i).2 := not_ne_iff.mp h'
    exact (h (by simpa [rowGroup,colGroup,physicalCell,cell,h'] using he)).elim

structure Mode (i : Fin a) (p : ℕ) (mask : MaskFamily a b S) where
  page : Page a b S
  tile : Fin (2^(i.val+1))
  order : Fin (p-1)
  hot : rowGroup mask i (page,tileIndex i tile) ≠ colGroup mask i (page,tileIndex i tile)

def source (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) : S :=
  colGroup mask i (m.page,tileIndex i m.tile)

def target (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) :
    Page a b S × S := (m.page,rowGroup mask i (m.page,tileIndex i m.tile))

theorem source_distinct (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) :
    (target mask i m).2 ≠ source mask i m := m.hot

def rowBlock (mask : MaskFamily a b S) (i : Fin a) (w : Physical a b S) : Page a b S × S :=
  (w.1,rowGroup mask i w)

theorem targeted_row_bit (mask : MaskFamily a b S) (i : Fin a) {p : ℕ}
    (w : Physical a b S) (m : Mode i p mask) (h : rowBlock mask i w = target mask i m) :
    w.2.val.testBit i.val=m.tile.val.testBit i.val := by
  have hpage := congrArg Prod.fst h
  have hg := congrArg Prod.snd h
  change rowGroup mask i w = rowGroup mask i (m.page,tileIndex i m.tile) at hg
  have hs : rowGroup mask i (m.page,w.2) ≠ colGroup mask i (m.page,tileIndex i m.tile) := by
    change w.1=m.page at hpage
    have he : (m.page,w.2)=w := Prod.ext hpage.symm rfl
    rw [he,hg]
    exact m.hot
  exact different_groups_same_bit mask m.page i w.2 (tileIndex i m.tile) hs

/-- Descendant scopes are drawn from the genuine real ports of the
tile, not from a separate complete cube of column coordinates. -/
theorem column_source_group {P : Type*} [Fintype P] (site : P → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask)
    [DecidableEq (Page a b S)] (q : P)
    (hq : q∈columns (fun q => (site q).1) (fun q => (site q).2.val) i.val m.page m.tile.val) :
    colGroup mask i (site q) = source mask i m := by
  obtain ⟨hp,_,hb⟩ := in_tile_exact (fun q => (site q).1) (fun q => (site q).2.val)
    i.val m.page m.tile.val q hq
  have h := cell_same_bit mask m.page i (site q).2 (tileIndex i m.tile) hb
  have he : (m.page,(site q).2)=site q := Prod.ext hp.symm rfl
  rw [he] at h
  exact congrArg Prod.snd h

#print axioms different_groups_same_bit
#print axioms targeted_row_bit
#print axioms column_source_group
end J6R9PacketScopes
