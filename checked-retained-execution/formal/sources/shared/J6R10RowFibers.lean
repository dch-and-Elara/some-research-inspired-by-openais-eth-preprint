import J6R10RowClassify
import J6R9PacketChild
import Mathlib.Tactic

/-! Reindexing the actual modes attached to one real column, without
assuming that every tile contains a real column. -/
namespace J6R10RowFibers
open scoped BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R10RowClassify J6R9PacketTiles
variable {S R : Type*} [LinearOrder S] [AddCommMonoid R] {a b : ℕ}

def atTile (mask : MaskFamily a b S) (i : Fin a) {p : ℕ}
    (y : Physical a b S) (m : Mode i p mask) : Prop :=
  y.1=m.page ∧ tileOf i y.2=m.tile

theorem exact_mode_fiber (mask : MaskFamily a b S) (i : Fin a) (p : ℕ)
    [Fintype (Page a b S)] (w y : Physical a b S)
    (hp : y.1=w.1) (hg : colGroup mask i y≠rowGroup mask i w)
    (f : Mode i p mask → R) :
    (∑ m ∈ Finset.univ.filter (atTile mask i y),f m) =
      ∑ n : Fin (p-1), f (actualMode mask i w y hp hg n) := by
  classical
  refine Finset.sum_bij' (fun m _ => m.order) (fun n _ => actualMode mask i w y hp hg n)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl) ?_
  · intro n _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl,rfl⟩
  · intro m hm
    obtain ⟨hmP,hmT⟩ := (Finset.mem_filter.mp hm).2
    exact mode_address_ext mask i _ _ hmP hmT rfl
  · intro m hm
    obtain ⟨hmP,hmT⟩ := (Finset.mem_filter.mp hm).2
    exact congrArg f (mode_address_ext mask i _ _ hmP.symm hmT.symm rfl)

theorem cross_bit (mask : MaskFamily a b S) (i : Fin a) (w y : Physical a b S)
    (hp : y.1=w.1) (hg : colGroup mask i y≠rowGroup mask i w) :
    w.2.val.testBit i.val=(tileOf i y.2).val.testBit i.val := by
  have e : (y.1,w.2)=w := Prod.ext hp rfl
  have h : rowGroup mask i (y.1,w.2) ≠ colGroup mask i (y.1,y.2) := by
    rw [e]
    exact hg.symm
  exact (different_groups_same_bit mask y.1 i w.2 y.2 h).trans (bit_of_tile i.val y.2.val)

theorem mem_tile_iff {Q : Type*} [Fintype Q] (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) (q : Q) :
    q∈columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val ↔
      atTile mask i (κ q) m := by
  classical
  unfold atTile columns
  constructor
  · intro h
    obtain ⟨hP,hT⟩ := (Finset.mem_filter.mp h).2
    exact ⟨hP,Fin.ext hT⟩
  · rintro ⟨hP,hT⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP,congrArg Fin.val hT⟩

#print axioms exact_mode_fiber
#print axioms cross_bit
#print axioms mem_tile_iff
end J6R10RowFibers
