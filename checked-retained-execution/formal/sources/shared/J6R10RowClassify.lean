import J6R9PacketScopes
import Mathlib.Tactic

/-! Each actual crossing column determines exactly one hot packet/tile
fiber for each surviving order. This includes the literal printed shift-mask
orientation in P11FullPackingPlacement. -/
namespace J6R10RowClassify
open P11FullPacking J6R9PacketScopes J6R9PacketTiles
variable {S : Type*} [LinearOrder S] {a b : ℕ}

def tileOf (i : Fin a) (y : Fin (2^a)) : Fin (2^(i.val+1)) :=
  ⟨tile i.val y.val,(tile_coordinates i.val y.val).1⟩

theorem col_cell_tile (mask : MaskFamily a b S) (i : Fin a) (y : Physical a b S)
    (τ : Fin (2^(i.val+1))) (h : tileOf i y.2=τ) :
    physicalCell mask y i=physicalCell mask (y.1,tileIndex i τ) i := by
  have hbit := bit_of_tile i.val y.2.val
  have ht := congrArg Fin.val h
  change tile i.val y.2.val=τ.val at ht
  rw [ht] at hbit
  exact cell_same_bit mask y.1 i y.2 (tileIndex i τ) hbit

theorem target_col_cross (mask : MaskFamily a b S) (i : Fin a) {p : ℕ}
    (w y : Physical a b S) (m : Mode i p mask)
    (hpage : y.1=m.page) (htile : tileOf i y.2=m.tile)
    (htarget : rowBlock mask i w=target mask i m) :
    y.1=w.1 ∧ colGroup mask i y≠rowGroup mask i w := by
  have ht := congrArg Prod.fst htarget
  change w.1=m.page at ht
  have hcol := congrArg (fun x : S × S => x.2) (col_cell_tile mask i y m.tile htile)
  have hr := congrArg Prod.snd htarget
  change rowGroup mask i w=rowGroup mask i (m.page,tileIndex i m.tile) at hr
  change colGroup mask i y=colGroup mask i (y.1,tileIndex i m.tile) at hcol
  rw [hpage] at hcol
  exact ⟨hpage.trans ht.symm,(by simpa only [hcol,hr] using m.hot.symm)⟩

private theorem align_cross (mask : MaskFamily a b S) (i : Fin a) (w y : Physical a b S)
    (hp : y.1=w.1) (hg : colGroup mask i y≠rowGroup mask i w) :
    rowGroup mask i w=rowGroup mask i (y.1,tileIndex i (tileOf i y.2)) ∧
    colGroup mask i y=colGroup mask i (y.1,tileIndex i (tileOf i y.2)) := by
  have hpos : (y.1,w.2)=w := Prod.ext hp rfl
  have hcross : rowGroup mask i (y.1,w.2) ≠ colGroup mask i (y.1,y.2) := by
    rw [hpos]
    exact hg.symm
  have hb := different_groups_same_bit mask y.1 i w.2 y.2 hcross
  have hc := cell_same_bit mask y.1 i w.2 y.2 hb
  rw [hpos] at hc
  have hd := col_cell_tile mask i y (tileOf i y.2) rfl
  exact ⟨congrArg Prod.fst (hc.trans hd),congrArg Prod.snd hd⟩

def actualMode (mask : MaskFamily a b S) (i : Fin a) (w y : Physical a b S)
    (hp : y.1=w.1) (hg : colGroup mask i y≠rowGroup mask i w)
    {p : ℕ} (n : Fin (p-1)) : Mode i p mask :=
  ⟨y.1,tileOf i y.2,n,by
    rw [← (align_cross mask i w y hp hg).1,← (align_cross mask i w y hp hg).2]
    exact hg.symm⟩

theorem actualMode_targets (mask : MaskFamily a b S) (i : Fin a) (w y : Physical a b S)
    (hp : y.1=w.1) (hg : colGroup mask i y≠rowGroup mask i w)
    {p : ℕ} (n : Fin (p-1)) :
    rowBlock mask i w=target mask i (actualMode mask i w y hp hg n) := by
  exact Prod.ext hp.symm (align_cross mask i w y hp hg).1

theorem mode_address_ext (mask : MaskFamily a b S) (i : Fin a) {p : ℕ}
    (m n : Mode i p mask) (hp : m.page=n.page) (ht : m.tile=n.tile) (hb : m.order=n.order) :
    m=n := by
  cases m
  cases n
  simp_all

theorem target_iff_cross (mask : MaskFamily a b S) (i : Fin a) {p : ℕ}
    (w y : Physical a b S) (m : Mode i p mask) (hp : y.1=m.page) (ht : tileOf i y.2=m.tile) :
    rowBlock mask i w=target mask i m ↔
      y.1=w.1 ∧ colGroup mask i y≠rowGroup mask i w := by
  refine ⟨target_col_cross mask i w y m hp ht,?_⟩
  rintro ⟨hpg,hg⟩
  have he : m=actualMode mask i w y hpg hg m.order :=
    mode_address_ext mask i m _ hp.symm ht.symm rfl
  rw [he]
  exact actualMode_targets mask i w y hpg hg m.order

#print axioms col_cell_tile
#print axioms target_col_cross
#print axioms actualMode_targets
#print axioms target_iff_cross
end J6R10RowClassify
