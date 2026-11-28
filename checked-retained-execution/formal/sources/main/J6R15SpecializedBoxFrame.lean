import J6R15SpecializedBoxNativeBase
import J6R14SpecializedBoxTileMoment
import J9R13PhysicalFusion

/-! Literal source and baseline factors on the same parent column
assignment, at every retained binary node. These are the actual
moment and same-group affine baseline used by the selected R12 mode. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R9PacketScopes J6R9PacketChild J6R10RowLocal
open J6R9Recursive J8Physical J8EndToEnd J8J9Grouped NativeProbeRing DyadicProbeCompiler

noncomputable section
variable {G R S V : Type*} [LinearOrder G] {P : V→Type*} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G P (2^a))
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype (Page a b G)] [DecidableEq (Page a b G)]
variable [(v : V)→Fintype (P v)] [(v : V)→DecidableEq (P v)]
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ x, rowGroup mask i (d.seat x) = d.rowLabel x.1)
variable (hc : ∀ x, colGroup mask i (d.seat x) = actualColLabel d x)

set_option linter.unusedSectionVars false in
include hr hc in
theorem genuine_samepage_box (e : EndpointSeating d) (even : Even (2^a)) (F : OldTables d)
    (p ell : ℕ) (f : ℤ[X]) (hnil : (2:Box f ell p)^p=0) (z : Scalar p f)
    (X : Wire R→Bool) (x : Wire R) :
    evalBox p f ell z
      (physicalBase d e even (J9FactorBounds.kernel (2^a))
        (fun g v r leg => (genuineBase d a g v r leg).divX)
        (d.rowLabel x.1) (localLabels d (d.rowLabel x.1) X) ⟨x.1,rfl⟩ x.2) =
      localValue d.seat mask i ((2^a:ℕ)-1:ℤ) p hnil
        (J6ActiveInterpolation.scalarIn p f ell z) (d.seat x) (fun y => X y.val) := by
  let g := d.rowLabel x.1
  let Y := cubeLabels d (onlyGroup d g (localLabels d g X))
  let Z := fun h => localLabels d h X
  have hSame : onlyGroup d g (localLabels d g X) g = Z g := onlyGroup_here d g _
  have hY : localWHalf d a g Y x = localWHalf d a g X x := by
    unfold localWHalf
    refine Finset.sum_congr rfl ?_
    intro y _
    by_cases hy : (d.seat x).1=(d.seat y).1 ∧ actualColLabel d y=g
    · rw [if_pos hy, if_pos hy]
      have h := cube_bit_owned d g _ Z hSame y hy.2
      rw [localLabels_cube d X y] at h
      rw [show Y y = X y from h]
    · rw [if_neg hy,if_neg hy]
  rw [genuine_base_is_own_divX d a rfl e even F]
  change evalBox p f ell z (localWHalf d a g Y x) = _
  rw [hY,localWHalf_eval d a p ell f hnil z g X x,
    local_as_filter d.seat mask i _ p hnil _ (d.seat x) X]
  refine Finset.sum_congr rfl ?_
  intro y _
  unfold columnEntry
  rw [hc y,hr x]
  by_cases hp : (d.seat x).1=(d.seat y).1
  · by_cases hg : actualColLabel d y=g
    · simp [hp,hg,g]
    · simp [hp,hg,g]
  · simp [hp,Ne.symm hp]

set_option linter.unusedSectionVars false in
theorem actual_tile_moment_box (hi : i.val=0) (p ell : ℕ) (f : ℤ[X]) (z : Scalar p f)
    (s : S) (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s) (X : Wire R→Bool)
    (n : Fin (Fintype.card (PinTile d s))) (hN : n.val<p-1) :
    let m := anchoredMode d mask i hr hc s off (⟨n.val,hN⟩:Fin (p-1))
    (moment d.seat mask i m (fun y => X y.val) : Box f ell p) =
      evalBox p f ell z (C (integralFeature d s n (localLabels d (d.pinLabel s) X))) := by
  dsimp only
  rw [moment_exact]
  have ht : (anchorTile d i s).val = (d.seat (pinWire d s)).2.val % 2 := by
    change J6R9PacketTiles.tile i.val _ = _
    rw [hi]
    rfl
  change (@J6R9PacketTiles.L (Wire R) (Page a b G) (Box f ell p) _ (Classical.decEq _) _
      (fun x => (d.seat x).1) (fun x => (d.seat x).2.val) i.val
      (d.seat (pinWire d s)).1 (anchorTile d i s).val n.val X : Box f ell p) = _
  rw [ht,hi]
  let ψ := (J6ActiveInterpolation.scalarIn p f ell).comp (toScalar p f)
  change _ = J6ActiveInterpolation.scalarIn p f ell
    ((C (integralFeature d s n (localLabels d (d.pinLabel s) X))).eval₂ (toScalar p f) (2*z))
  rw [eval₂_C]
  change _ = ψ (integralFeature d s n (fun q => X (pinWire d q.val),localBitsFromWire d (d.pinLabel s) X))
  rw [← same_tile_moment_literal d s n X]
  unfold J6R9PacketTiles.L
  rw [map_sum]
  refine Finset.sum_congr (Finset.ext (fun q => by simp [J6R9PacketTiles.columns])) ?_
  intro y _
  rw [map_mul,map_pow,map_natCast]
  cases X y <;> simp [J6R9PacketTiles.bit]

#print axioms genuine_samepage_box
#print axioms actual_tile_moment_box
end
end J6R14SpecializedBox