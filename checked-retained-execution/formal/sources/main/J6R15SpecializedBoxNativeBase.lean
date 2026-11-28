import J6R15SpecializedBoxNativeKernel
import J6R14SpecializedBoxModeChart
import J8J9GroupedCube
import J6R10RowLocal

/-! Literal same-page baseline for the real outer-node column incidences.
Only the actual group-owned wires enter the sum, so extending a local
assignment by zero elsewhere does not introduce a new source table. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P1DyadicGrid
open J8Physical J8EndToEnd J8J9Grouped DyadicProbeCompiler NativeProbeRing
open J6R9Recursive J6R9PacketScopes P11FullPacking

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def onlyGroup (g : G) (x : J8J9Grouped.Assignment d g) : Cube d :=
  fun j => if h : j=g then h.symm ▸ x else (fun _ => false,fun _ _ => false)

set_option linter.unusedSectionVars false in
theorem onlyGroup_here (g : G) (x : J8J9Grouped.Assignment d g) :
    onlyGroup d g x g = x := by simp [onlyGroup]

set_option linter.unusedSectionVars false in
theorem cube_bit_owned (g : G) (x y : Cube d) (h : x g=y g)
    (w : Wire R) (hw : actualColLabel d w=g) :
    cubeLabels d x w = cubeLabels d y w := by
  unfold actualColLabel at hw
  unfold cubeLabels
  cases hh : d.column w with
  | inl s =>
    rw [hh] at hw
    change d.pinLabel s=g at hw
    rw [←hw] at h
    exact congrArg (fun z : J8J9Grouped.Assignment d (d.pinLabel s) => z.1 ⟨s,rfl⟩) h
  | inr v =>
    rcases v with ⟨v,q⟩
    rw [hh] at hw
    change d.colLabel v=g at hw
    rw [←hw] at h
    exact congrArg (fun z : J8J9Grouped.Assignment d (d.colLabel v) => z.2 ⟨v,rfl⟩ q) h

def localWHalf (a : ℕ) (g : G) (X : Wire R→Bool) (x : Wire R) : Source[X] :=
  ∑ y : Wire R,
    if (d.seat x).1=(d.seat y).1 ∧ actualColLabel d y=g then
      ((WHalf a ((L:ℤ)-1) ((d.seat y).2.val-(d.seat x).2.val:ℤ)).map twoLocalToSource.toRingHom) *
        C (sourceBit (X y))
    else 0

set_option linter.unusedSectionVars false in
theorem localWHalf_const (a : ℕ) (hW : L=2^a) (even : Even L) (g : G)
    (X : Wire R→Bool) (r : LocalRow d g) (leg : Bool) :
    rationalMap ((localWHalf d a g X (r.1,leg)).coeff 0) =
      physicalArgument d X (r.1,leg) := by
  let x : Wire R := (r.1,leg)
  unfold localWHalf physicalArgument
  simp only [finset_sum_coeff,map_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  change rationalMap ((if (d.seat x).1=(d.seat y).1 ∧ actualColLabel d y=g then
      (WHalf a ((L:ℤ)-1) ((d.seat y).2.val-(d.seat x).2.val:ℤ)).map twoLocalToSource.toRingHom *
        C (sourceBit (X y)) else 0).coeff 0) =
      centerKernel d x y * NativeChildRealization.bitValue ℚ (X y)
  by_cases hp : (d.seat x).1=(d.seat y).1
  · by_cases hg : actualColLabel d y=g
    · rw [if_pos ⟨hp,hg⟩,mul_coeff_zero,coeff_map,coeff_C_zero,map_mul]
      have hw := same_native_W_at_extreme d a hW x y
      rw [if_pos hp,eval₂_at_zero] at hw
      change rationalMap (twoLocalToSource ((WHalf a ((L:ℤ)-1)
        ((d.seat y).2.val-(d.seat x).2.val:ℤ)).coeff 0)) * rationalMap (sourceBit (X y)) = _
      rw [source_rat_agrees,WHalf_coeff0,←hw]
      cases X y <;> simp [sourceBit,NativeChildRealization.bitValue]
    · have hs : ¬ Shift d x y := fun h =>
        hg ((shift_stays_in_child d even h).symm.trans r.prop)
      simp [hp,hg,centerKernel_exact,hs]
  · simp [hp,centerKernel]

def genuineBase (a : ℕ) : IntegralArguments d :=
  fun g x r leg => localWHalf d a g (cubeLabels d (onlyGroup d g x)) (r.1,leg)

set_option linter.unusedSectionVars false in
theorem genuine_base_is_own_divX (a : ℕ) (hW : L=2^a) (e : EndpointSeating d)
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

set_option linter.unusedSectionVars false in
theorem localWHalf_eval (a p ell : ℕ) (f : ℤ[X]) (hnil : (2:Box f ell p)^p=0)
    (z : Scalar p f) (g : G) (X : Wire R→Bool) (x : Wire R) :
    evalBox p f ell z (localWHalf d a g X x) =
      ∑ y : Wire R,
        if (d.seat x).1=(d.seat y).1 ∧ actualColLabel d y=g then
          (J6R9PacketLocal.W a ((L:ℤ)-1) ((d.seat y).2.val-(d.seat x).2.val:ℤ)).eval₂
            (J6ZeroTransport.reduceAt p hnil) (J6ActiveInterpolation.scalarIn p f ell z) *
              J6R9PacketTiles.bit (Box f ell p) (X y)
        else 0 := by
  rw [localWHalf,map_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  by_cases hh : (d.seat x).1=(d.seat y).1 ∧ actualColLabel d y=g
  · rw [if_pos hh,if_pos hh,map_mul]
    congr 1
    · change J6ActiveInterpolation.scalarIn p f ell
        (((WHalf a ((L:ℤ)-1) ((d.seat y).2.val-(d.seat x).2.val:ℤ)).map
          twoLocalToSource.toRingHom).eval₂ (toScalar p f) (2*z)) = _
      rw [native_eval_transports, map_mul,map_ofNat,WHalf_eval_twice]
    · cases X y <;> simp [sourceBit,J6R9PacketTiles.bit]
  · rw [if_neg hh,if_neg hh,map_zero]

#print axioms onlyGroup
#print axioms cube_bit_owned
#print axioms localWHalf_const
#print axioms genuine_base_is_own_divX
#print axioms localWHalf_eval
end
end J6R14SpecializedBox
