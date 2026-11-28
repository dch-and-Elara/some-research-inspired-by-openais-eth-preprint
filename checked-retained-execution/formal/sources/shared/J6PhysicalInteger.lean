import J6OrientedHostEval
import J6FactorToInteger
import J6RepairedCapacity

/-! Check the printed J6 normalization on the repaired packing, using real
per-column padding loads instead of the ordered-cell capacity chart. -/
namespace J6PhysicalInteger
open scoped BigOperators Polynomial Classical
open P11FullPacking J6Mesh J6RepairedCentered J6OrientedHost J6OrientedHostEval
open J6IntegerLayers J6NativeHeightMesh J6ZeroTransport J6RecursiveOrientationLocal

set_option maxHeartbeats 3500000
variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V]

noncomputable def loads
    (m l : ℕ) (mask : MaskFamily (a m) (K m) S)
    (w : Fin (a m) → S) (h : m≤K m) (hL : 2*l=L m) :
    J6Recovery.Addr m → Pad w m (K m) l → ℕ :=
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  fun i p => J6OrientedPadding.count (padShift mask w h hL (index m i)) p

theorem physical_layer_eq
    (m l q : ℕ) (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hL : 2*l=L m) (T : Plant V m q)
    (hzero : coreA T (fun _ => false)=true) (i : J6Recovery.Addr m) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    J6NativeHeightClearing.rationalSlot (oldOK T w) (newOK T w)
      (fun p x => ((shiftAt m l mask w h hL i p).map x).getD false) (point m i) =
    J6Recovery.layerSum m q (oldWeight (coreA T)) (oldWeight (coreB T))
      (loads m l mask w h hL) i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have hk := (address_index m i).2.2.2
  have ht : index m i ≤ 2*l := by omega
  rw [J6Recovery.layerSum_factorization]
  unfold shiftAt
  have hB : (∑ x : Fin m→Bool, J6OrientedPlantValue.wt (coreB T) x) = (2:ℚ)^q :=
    coreB_count T
  have hE : 2*l-index m i = J6Recovery.exp m i := by unfold J6Recovery.exp; rw [hL]
  rw [actual_layer_factorization T mask w h hL _ ht (point m i),hE,hB]
  have hw : J6OrientedPlantValue.wt (coreA T) (fun _ => false)=1 := by
    simp [J6OrientedPlantValue.wt,hzero]
  rw [hw,one_pow,mul_one,← pow_mul]
  unfold J6Recovery.publicFactor J6Recovery.exp loads
  change ((LayerRecovery.layerPolynomial (oldWeight (coreA T)) (oldWeight (coreB T))).eval (point m i))^_ *
      (2:ℚ)^(q*index m i) * _ = _
  ac_rfl

theorem printed_receiver_no_fit_assumption
    (m base l q : ℕ) (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hL : 2*l=L m) (T : Plant V m q)
    (hzero : coreA T (fun _ => false)=true) (i : J6Recovery.Addr m)
    (hS : Fintype.card S=64) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    let p := J6SourcePrecision.printed m base
    let n := sampleNum m i
    let d := sampleDen m i
    let z := J6NativeHeightResidue.residueSlot (oldOK T w) (newOK T w)
        (fun p x => ((shiftAt m l mask w h hL i p).map x).getD false)
        (reduceBase p (J6NativeHeightDyadic.scalar m i))
    J6IntegerDecode.integerDecode p (J6Recovery.exp m i) (M m) d
      (factor (P:=Fin m) n d (index m i) q (loads m l mask w h hL i)) z =
      (oldLayer (coreA T) (coreB T) n d,p) := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  have hCard : Fintype.card (Ports m l w) =
      (index m i + J6Recovery.exp m i)*Fintype.card (Fin m) + 2*Fintype.card (Pad w m (K m) l) := by
    have he := (address_index m i).2.2.2
    have hsum : index m i + J6Recovery.exp m i = L m := by unfold J6Recovery.exp; omega
    rw [hsum,Fintype.card_fin,← hL,Nat.mul_comm (2*l) m]
    exact wire_cardinality (m:=m) (b:=K m) (l:=l) w
  have hcount : ∀ v, loads m l mask w h hL i v ≤ 2 := by
    intro v
    unfold loads
    apply J6OrientedPadding.count_le_two
    intro p r q hp hr
    exact Sum.inr_injective
      (J6OrientedShift.successor_injective mask w h hL (index m i) _ _ _
        (padShift_apply mask w h hL (index m i) p q hp)
        (padShift_apply mask w h hL (index m i) r q hr))
  exact J6FactorToInteger.receiver_factorization _ _ _ (coreA T) (coreB T)
    m base q (loads m l mask w h hL) i
    hcount
    (J6RepairedCapacity.actual_wire_count m l w h hL hS) hCard
    (physical_layer_eq m l q mask w h hL T hzero i)

#print axioms physical_layer_eq
#print axioms printed_receiver_no_fit_assumption
end J6PhysicalInteger