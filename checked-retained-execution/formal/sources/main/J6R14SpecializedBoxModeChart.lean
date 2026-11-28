import J6R10RowAffine
import J6RecursiveMenu
import J6R14SpecializedBoxParentFile

/-! Same-address bridge for the actual J9 pinned tile and the printed
J6 mode alphabet at valuation zero. The two owner equalities in this
abstract chart are the ones furnished by the preserved R13 physical
packing; no equality of aggregate contractions is postulated. -/
namespace J6R14SpecializedBox
open scoped Classical BigOperators
open P11FullPacking J6R9PacketScopes J8Physical

noncomputable section
variable {G R S V : Type*} [LinearOrder G] {P : V→Type*} {a b p : ℕ}
variable (d : Layout (Page a b G) R S V G P (2^a))
variable (mask : MaskFamily a b G) (i : Fin a)

def anchorTile (s : S) : Fin (2^(i.val+1)) :=
  ⟨J6R9PacketTiles.tile i.val (d.seat (pinWire d s)).2.val,
    (J6R9PacketTiles.tile_coordinates i.val _).1⟩

theorem anchor_same_cell (s : S) :
    physicalCell mask ((d.seat (pinWire d s)).1,tileIndex i (anchorTile d i s)) i =
      physicalCell mask (d.seat (pinWire d s)) i := by
  have hh := J6R9PacketTiles.bit_of_tile i.val (d.seat (pinWire d s)).2.val
  exact (cell_same_bit mask _ i _ _ hh).symm

variable (hr : ∀ x, rowGroup mask i (d.seat x) = d.rowLabel x.1)
variable (hc : ∀ x, colGroup mask i (d.seat x) = actualColLabel d x)

def anchoredMode (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (order : Fin (p-1)) : Mode i p mask :=
  ⟨(d.seat (pinWire d s)).1,anchorTile d i s,order,by
    unfold rowGroup colGroup
    rw [anchor_same_cell d mask i s]
    exact fun h => off ((hr _).symm.trans (h.trans ((hc _).trans (pinWire_colLabel d s))))⟩

theorem anchored_source (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (p-1)) :
    source mask i (anchoredMode d mask i hr hc s off n) = d.pinLabel s := by
  change colGroup mask i ((d.seat (pinWire d s)).1,tileIndex i (anchorTile d i s)) = _
  unfold colGroup
  rw [anchor_same_cell d mask i]
  exact (hc _).trans (pinWire_colLabel d s)

theorem anchored_target (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (p-1)) :
    target mask i (anchoredMode d mask i hr hc s off n) =
      ((d.seat (pinWire d s)).1, d.rowLabel (pinWire d s).1) := by
  refine Prod.ext ?_ ?_
  · rfl
  change rowGroup mask i ((d.seat (pinWire d s)).1,tileIndex i (anchorTile d i s)) = _
  unfold rowGroup
  rw [anchor_same_cell d mask i]
  exact hr _

private theorem parity_of_sameBit {x y : ℕ} (h : x.testBit 0=y.testBit 0) :
    x%2=y%2 := by
  by_cases hx : x.testBit 0 = true
  · have hy := h.symm.trans hx
    exact (Nat.mod_two_eq_one_iff_testBit_zero.mpr hx).trans
      (Nat.mod_two_eq_one_iff_testBit_zero.mpr hy).symm
  · have hx' := Bool.eq_false_of_not_eq_true hx
    have hy' := h.symm.trans hx'
    exact (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hx').trans
      (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hy').symm

variable [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
theorem anchored_actual_target_iff (hi : i.val=0)
    (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (p-1)) (x : Wire R) :
    rowBlock mask i (d.seat x) = target mask i (anchoredMode d mask i hr hc s off n) ↔
      x ∈ targets d (pinWire d s) := by
  constructor
  · intro hx
    have hp := congrArg Prod.fst (hx.trans (anchored_target d mask i hr hc s off n))
    have hg := congrArg Prod.snd (hx.trans (anchored_target d mask i hr hc s off n))
    change rowGroup mask i (d.seat x) = d.rowLabel (pinWire d s).1 at hg
    rw [hr] at hg
    have hbit := targeted_row_bit mask i _ _ hx
    change (d.seat x).2.val.testBit i.val = (anchorTile d i s).val.testBit i.val at hbit
    have hpar : (d.seat x).2.val%2=(d.seat (pinWire d s)).2.val%2 := by
      apply parity_of_sameBit
      rw [← hi]
      exact hbit.trans (J6R9PacketTiles.bit_of_tile i.val (d.seat (pinWire d s)).2.val).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hpar,by
      rw [hg,pinWire_colLabel]
      exact off⟩
  · intro hx
    obtain ⟨hp,hpar,_⟩ := (Finset.mem_filter.mp hx).2
    rw [anchored_target d mask i hr hc s off n]
    refine Prod.ext hp ?_
    change rowGroup mask i (d.seat x) = d.rowLabel (pinWire d s).1
    rw [hr,d.rowOrientation x,d.rowOrientation (pinWire d s),hp,hpar]

omit [Fintype R] [DecidableEq R] in
theorem anchored_singleton_legal [Fintype (Page a b G)]
    (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (p-1)) :
    Finsupp.single (anchoredMode d mask i hr hc s off n) 1 ∈
      J6RecursiveMenu.menu p (J6R10RowAffine.weight i p mask) := by
  classical
  let m := anchoredMode d mask i hr hc s off n
  rw [J6RecursiveMenu.exact_printed_menu p _ (fun x => x.order.val.succ_pos)]
  unfold J6RecursiveMenu.weighted
  change (∑ j : Mode i p mask, J6R10RowAffine.weight i p mask j * Finsupp.single m 1 j) < p
  rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (fun j _ hj => by simp [Finsupp.single_eq_of_ne hj])]
  simp only [Finsupp.single_eq_same,mul_one,J6R10RowAffine.weight]
  change n.val+1<p
  have hn := n.isLt
  omega

#print axioms anchor_same_cell
#print axioms anchoredMode
#print axioms anchored_source
#print axioms anchored_target
#print axioms anchored_actual_target_iff
#print axioms anchored_singleton_legal
end
end J6R14SpecializedBox
