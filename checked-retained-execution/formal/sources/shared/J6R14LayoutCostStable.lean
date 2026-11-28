import J6R14LayoutCostUnique

/-! The raw coordinate layout has a single global injective typed
address, including across two different orientations of one key. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape P11FullPacking

abbrev AddressRank (a pages q : ℕ) :=
  Cell (Fin a) (Fin 64) × Fin (min (2^q) (pages*2^a))

noncomputable def stableAddr {a pages q : ℕ} (ha : a≤q) (x : AddressRank a pages q) :
    Physical a pages (Fin 64) :=
  let r := encodeBits q x.2.val
  let d := seatWords (marksOf x.1) r
  let hp : bitsValue d.result.page<pages :=
    page_in_range (marksOf x.1) r (by rw [marksOf_len,encodeBits_length]; exact ha) pages
      (by rw [marksOf_len,encodeBits_exact _ _ (x.2.isLt.trans_le (min_le_left _ _))]
          exact x.2.isLt.trans_le (min_le_right _ _))
  decodePhysical x.1 d.result hp

theorem stableAddr_cell {a pages q : ℕ} (ha : a≤q) (x : AddressRank a pages q) :
    physicalCell (fun _ _ _ => false) (stableAddr ha x)=x.1 :=
  (realPhysical_single x.1 (encodeBits q x.2.val) (by rwa [encodeBits_length])
    (by rw [encodeBits_exact _ _ (x.2.isLt.trans_le (min_le_left _ _))]
        exact x.2.isLt.trans_le (min_le_right _ _))).1

theorem stableAddr_injective {a pages q : ℕ} (ha : a≤q) :
    Function.Injective (stableAddr (a:=a) (pages:=pages) (q:=q) ha) := by
  intro x y H
  have hc : x.1=y.1 := by
    have E := congrArg (physicalCell (fun _ _ _ => false)) H
    rwa [stableAddr_cell,stableAddr_cell] at E
  obtain ⟨c,i⟩ := x
  obtain ⟨d,j⟩ := y
  change c=d at hc
  subst d
  let r := encodeBits q i.val
  let s := encodeBits q j.val
  have hi : i.val<2^q := i.isLt.trans_le (min_le_left _ _)
  have hj : j.val<2^q := j.isLt.trans_le (min_le_left _ _)
  have R : r=s := realPhysical_cell_injective c r s
    (by rwa [encodeBits_length]) (by rw [encodeBits_length,encodeBits_length])
    (by rw [encodeBits_exact _ _ hi]; exact i.isLt.trans_le (min_le_right _ _))
    (by rw [encodeBits_exact _ _ hj]; exact j.isLt.trans_le (min_le_right _ _))
    H
  have Q := congrArg bitsValue R
  have hJ : i=j := Fin.ext ((encodeBits_exact q i.val hi).symm.trans
    (Q.trans (encodeBits_exact q j.val hj)))
  rw [hJ]

#print axioms stableAddr_cell
#print axioms stableAddr_injective
end J6R14LayoutCost

