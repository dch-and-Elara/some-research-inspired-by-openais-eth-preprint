import J6PhysicalInteger
import J6ZeroTransportSource

/-! The rational value is represented by one genuine odd-local element
whose images in Q and in every finite receiving ring are compared
separately. No map from Q to a finite characteristic ring is asserted. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6RepairedCentered
open J6OrientedHost J6OrientedHostEval J6NativeHeightResidue J6NativeHeightClearing
open J6ZeroTransport
noncomputable section

theorem residue_rat {E : Type*} [Fintype E] [DecidableEq E]
    (A B : (E→Bool)→Bool) (read : E → (E→Bool) → Bool) (c : ℚ) :
    residueSlot A B read c = rationalSlot A B read c := by
  unfold residueSlot rationalSlot
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  split
  · refine Finset.prod_congr rfl fun r _ => ?_
    cases hy : y r <;> cases hx : read r x <;>
      simp [ringEntry,LayerRecovery.wireFactor]
  · rfl

theorem residue_rat_any {E : Type*} (F F' : Fintype E) (D D' : DecidableEq E)
    (A B : (E→Bool)→Bool) (read : E → (E→Bool) → Bool) (c : ℚ) :
    @residueSlot ℚ E _ F D A B read c = @rationalSlot E F' D' A B read c := by
  have hF : F=F' := Subsingleton.elim _ _
  have hD : D=D' := Subsingleton.elim _ _
  subst F'
  subst D'
  exact @residue_rat E F D A B read c

variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V]

/-- The actual oriented partial matrix and the original literal two-sided
gates, lifted over the two-local integers before taking any finite image. -/
def plantedScalar (m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m) (i : Fin (m+1)) : TwoLocal :=
  literalContraction (fun r s : Ports m l w =>
    if shiftAt m l mask w hm hL i r=some s then J6NativeHeightDyadic.scalar m i else 0)
    (oldOK T w) (newOK T w)

theorem plantedScalar_receives {R : Type*} [CommRing R] (φ : TwoLocal →+* R)
    (m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m) (i : Fin (m+1)) :
    φ (plantedScalar m l q T w mask hm hL i) =
      residueSlot (oldOK T w) (newOK T w) (fun r x => ((shiftAt m l mask w hm hL i r).map x).getD false)
        (φ (J6NativeHeightDyadic.scalar m i)) := by
  rw [plantedScalar,map_literalContraction]
  have hW : (fun r s : Ports m l w =>
      φ (if shiftAt m l mask w hm hL i r=some s then J6NativeHeightDyadic.scalar m i else 0)) =
      (fun r s : Ports m l w =>
        if shiftAt m l mask w hm hL i r=some s then φ (J6NativeHeightDyadic.scalar m i) else 0) := by
    funext r s
    split <;> simp
  rw [hW,contraction_of_partial]

set_option maxHeartbeats 3200000 in
/-- Formula (J2), including the exact oriented padding loads. The all-zero
planted left assignment is an explicit hypothesis, exactly as in J6. -/
theorem plantedScalar_J2 (m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m)
    (hzero : coreA T (fun _ => false)=true) (i : Fin (m+1)) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    twoLocalRat (plantedScalar m l q T w mask hm hL i) =
      J6Recovery.layerSum m q (J6IntegerLayers.oldWeight (coreA T))
        (J6IntegerLayers.oldWeight (coreB T)) (J6PhysicalInteger.loads m l mask w hm hL) i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let c := J6NativeHeightDyadic.scalar m i
  have hr := plantedScalar_receives twoLocalRat m l q T w mask hm hL i
  have hJ := J6PhysicalInteger.physical_layer_eq m l q mask w hm hL T hzero i
  exact hr.trans (Eq.trans (residue_rat_any _ _ _ _ _ _ _ _) hJ)

#print axioms residue_rat
#print axioms residue_rat_any
#print axioms plantedScalar
#print axioms plantedScalar_receives
#print axioms plantedScalar_J2
end
end J6R15PlantedIdentity
