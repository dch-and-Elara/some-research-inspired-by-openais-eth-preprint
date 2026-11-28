import J8RelaxedBase
import J6R15SpecializedBoxFrame
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace J8Physical.Relaxed
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P1DyadicGrid J6R14SpecializedBox
open J8EndToEnd J8J9Grouped DyadicProbeCompiler NativeProbeRing
open J6R9Recursive J6R9PacketScopes P11FullPacking J6R9PacketChild J6R10RowLocal
noncomputable section
section General
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype Packet] [DecidableEq Packet]
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [(v : V)→Fintype (P v)] [(v : V)→DecidableEq (P v)]
theorem physical_base_at_original_center (e : RowEndpointSeating d) (even : Even L)
    (F : OldTables d) (tail : IntegralArguments d) (g : G) (X : Wire R→Bool)
    (bits : LocalPin d g→Bool) (r : LocalRow d g) (leg : Bool) :
    rationalMap
      ((physicalBase d e even (J9FactorBounds.kernel L) tail g
        (bits,localBitsFromWire d g X) r leg).coeff 0) =
      physicalArgument d X (r.1,leg) := by
  have hL : 0 < L := (d.seat (r.1,leg)).2.isLt.pos
  have hc := printed_amplitude_integral L (by omega) even
  exact (constructed_base_agrees d e even (J9FactorBounds.kernel L) hc F tail
    g (bits,localBitsFromWire d g X) r leg).trans
      (center_to_compiled_argument d e even (F g) X r leg).symm

set_option linter.unusedSectionVars false in
theorem native_base_realized_by_own_tail (e : RowEndpointSeating d) (even : Even L)
    (B : IntegralArguments d)
    (h : ∀ g x r leg, (B g x r leg).coeff 0 =
      (physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0) g x r leg).coeff 0) :
    physicalBase d e even (J9FactorBounds.kernel L)
      (fun g x r leg => (B g x r leg).divX) = B := by
  funext g x r leg
  have h0 := h g x r leg
  simp only [physicalBase,mul_zero,add_zero,coeff_C_zero] at h0
  unfold physicalBase
  rw [← h0,add_comm,X_mul_divX_add]

theorem genuine_base_is_own_divX (a : ℕ) (hW : L=2^a) (e : RowEndpointSeating d)
    (he : Even L) (F : OldTables d) :
    physicalBase d e he (J9FactorBounds.kernel L)
      (fun g x r leg => (genuineBase d a g x r leg).divX) = genuineBase d a := by
  apply native_base_realized_by_own_tail d e he
  intro g x r leg
  apply rationalMap_injective
  unfold genuineBase
  rw [localWHalf_const d a hW he]
  let Y := cubeLabels d (onlyGroup d g x)
  have hl : localBitsFromWire d g Y=x.2 := by
    have h := (cubeLabels_local d (onlyGroup d g x) g).trans (onlyGroup_here d g x)
    exact congrArg Prod.snd h
  have h := physical_base_at_original_center d e he F (fun _ _ _ _=>0) g Y x.1 r leg
  rw [hl] at h
  exact h.symm

end General
section Physical
variable {G R S V : Type*} [LinearOrder G] {P : V→Type*} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G P (2^a))
variable [Fintype (Page a b G)] [DecidableEq (Page a b G)]
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
variable [(v : V)→Fintype (P v)] [(v : V)→DecidableEq (P v)]
variable (mask : MaskFamily a b G) (i : Fin a)
variable (hr : ∀ x, rowGroup mask i (d.seat x) = d.rowLabel x.1)
variable (hc : ∀ x, colGroup mask i (d.seat x) = actualColLabel d x)

set_option linter.unusedSectionVars false in
include hr hc in
theorem genuine_samepage_box (e : RowEndpointSeating d) (even : Even (2^a)) (F : OldTables d)
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

end Physical
#print axioms physical_base_at_original_center
#print axioms genuine_base_is_own_divX
#print axioms genuine_samepage_box
end
end J8Physical.Relaxed