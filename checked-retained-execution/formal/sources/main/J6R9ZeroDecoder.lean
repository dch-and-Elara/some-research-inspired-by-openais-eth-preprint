import J6PhysicalLeafOutput
import J6PhysicalInteger

/-! Literal J6 direct-leaf outputs read by the exact signed integer
routine, on the single repaired physical layout. -/
namespace J6R9ZeroDecoder
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6RepairedCentered J6OrientedHost J6OrientedHostEval
open J6RecursivePortCube J6RecursiveAssembly J6ZeroTransport J6NativeHeightMesh
open J6IntegerLayers J6IntegerDecode
set_option maxHeartbeats 5000000

variable {S V Mode : Type*} [LinearOrder S] [Fintype S] [Fintype V] [Fintype Mode] [DecidableEq Mode]

/-- Changing how equality of a finite port is decided does not change
the exact rational reduction. This aligns the instance implicit in the
leaf theorem with the instance of the signed recipient. -/
private theorem rational_slot_instances {P : Type*} [Fintype P]
    (a b : DecidableEq P) (A B : (P → Bool) → Bool)
    (read : P → (P → Bool) → Bool) (w : ℚ) :
    @J6NativeHeightClearing.rationalSlot P _ a A B read w =
      @J6NativeHeightClearing.rationalSlot P _ b A B read w := by
  have hb : a = b := Subsingleton.elim _ _
  subst b
  rfl

/-- Transfer equality of recovered rationals to equality of the actual
signed lifts on which the integer receive routine operates. No injectivity
of arbitrary residue lifts is needed. -/
private theorem same_integer_decode (p e N : ℕ) (d u : ℤ)
    (x y : ZMod (2^p)) (hd : (d:ℚ)^N ≠ 0)
    (h : ((((d:ZMod (2^p))^N*x).valMinAbs:ℚ)/(d:ℚ)^N) =
        ((((d:ZMod (2^p))^N*y).valMinAbs:ℚ)/(d:ℚ)^N)) :
    integerDecode p e N d u x = integerDecode p e N d u y := by
  have hmul := congrArg (fun z : ℚ => z*(d:ℚ)^N) h
  have hcast : (((d:ZMod (2^p))^N*x).valMinAbs:ℚ) =
      (((d:ZMod (2^p))^N*y).valMinAbs:ℚ) := by
    simpa only [div_mul_cancel₀ _ hd] using hmul
  have hraw := (Int.cast_injective (α:=ℚ)) hcast
  unfold integerDecode
  rw [hraw]

theorem decode_actual_leaf_root
    (m base l q : ℕ) (host : Plant V m q) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m)
    (i : Fin (m+1)) (hS : Fintype.card S=64)
    (hz : coreA host (fun _ => false)=true)
    (target source : Mode → S × Page (a m) (K m) S)
    (weights : Mode → ℕ) (hweights : ∀ k, 0 < weights k)
    (moment : ∀ g, GroupCube (groupOf m l mask w h hL) g → Mode → ZMod (2^J6SourcePrecision.printed m base))
    (H : ℕ) (n : S → ℕ)
    (order : ∀ g, Fin (n g) ≃ {q : Sum (Ports m l w) (Ports m l w) // groupOf m l mask w h hL q = g})
    (hSmall : ∀ g, n g ≤ H) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    let p := J6SourcePrecision.printed m base
    let shift := shiftAt m l mask w h hL i
    let group := groupOf m l mask w h hL
    let seat := slotPage m l mask w h hL
    let run := fun β g =>
      J6ChildPlan.run group seat target source (scopes (oldScope host w) (fun _ => Bool))
        (ports (rowPort host w) (colPort host w)) (owner w (coord m))
        (fun v y => if flag (rowTable host w) (colTable w) v y then 1 else 0)
        shift (reduceBase p (J6NativeHeightDyadic.scalar m i)) moment β g (n g) (order g)
    integerDecode p (J6Recovery.exp m i) (M m) (sampleDen m i)
      (factor (P:=Fin m) (sampleNum m i) (sampleDen m i) (index m i) q
          (J6PhysicalInteger.loads m l mask w h hL i))
      (∑ β ∈ J6RecursiveMenu.menu p weights, ∏ g, run β g) =
      (oldLayer (coreA host) (coreB host) (sampleNum m i) (sampleDen m i), p) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  dsimp only
  have hRun := J6PhysicalLeafOutput.correct_actual_leaf_root
    m base l q host mask w h hL i hS target source weights hweights moment H n order hSmall
  dsimp only at hRun
  let p := J6SourcePrecision.printed m base
  let read := fun (j : Ports m l w) (x : Ports m l w → Bool) =>
    ((shiftAt m l mask w h hL i j).map x).getD false
  let residue := J6NativeHeightResidue.residueSlot (oldOK host w) (newOK host w) read
    (reduceBase p (J6NativeHeightDyadic.scalar m i))
  have hDirect := J6NativeHeightLift.exact_centered_readout m base i
    (J6RepairedCapacity.actual_wire_count m l w h hL hS) (oldOK host w) (newOK host w) read
    (reduceBase p) residue rfl
  have hDen : (sampleDen m i:ℚ)^M m ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (mesh_bounds m i).1.ne')
  refine (same_integer_decode p (J6Recovery.exp m i) (M m) (sampleDen m i) _ _ residue hDen ?_).trans ?_
  · refine hRun.trans (Eq.trans ?_ hDirect.symm)
    apply rational_slot_instances
  · exact J6PhysicalInteger.printed_receiver_no_fit_assumption m base l q mask w h hL host hz i hS

#print axioms decode_actual_leaf_root
end J6R9ZeroDecoder