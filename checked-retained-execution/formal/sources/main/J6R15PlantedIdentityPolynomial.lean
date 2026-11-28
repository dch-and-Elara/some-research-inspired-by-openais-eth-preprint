import J6R15PlantedIdentityRoot
import J6R15PlantedIdentityCenter
import J6R14ZeroModeFallback

/-! On the identical selected physical root and the identical odd mesh
centre, the R14 zero-mode polynomial and the rational J2 formula refer
to one and the same element of the odd localization. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Repack J6R9Recursive
open J6R11Blueprint J6R12Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
noncomputable section

variable {V : Type} [Fintype V] {f : ℤ[X]} {ell : ℕ}
variable (base m l q native : ℕ) (T : Plant V m q)
variable (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
variable (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
variable (d : Ready (rootParams f ell m native) (sourceDelta (physicalSize m native))
  (physicalRootCall f ell base m l q T w))

set_option maxHeartbeats 4300000 in
theorem selected_zeroPolynomial_at_odd
    (i : Fin (m+1)) (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell) :
    let c := physicalRootCall f ell base m l q T w
    let sel := exactJ6Selector (f:=f) (ell:=ell) base m l q native T w mask hm hL hn
    let t := oddRootCenter f ell base m l q native T w hn i
    let p := registerPrecision (rootParams f ell m native) c t
    (J6R14ZeroMode.physicalZeroP sel d t hf).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (plantedScalar m l q T w mask hm hL i) := by
  let c := physicalRootCall f ell base m l q T w
  let S := rootParams f ell m native
  let t := oddRootCenter f ell base m l q native T w hn i
  let p := registerPrecision S c t
  let sel := exactJ6Selector (f:=f) (ell:=ell) base m l q native T w mask hm hL hn
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have ht := active_grid _ _ _ t.property
  change (J6R14ZeroMode.polynomial (packing sel d) (centerIndex d t) t.val p c.host.file hf).eval 0 = _
  exact (zero_eq_parentJet (packing sel d) (centerIndex d t) ht.1 ht.2 rfl p
    (J6R12Blueprint.register_positive d t) c.host.file hf).trans
    (selected_parent_at_odd base m l q native T w mask hm hL hn d i hf hbase hF hℓ)

set_option maxHeartbeats 4700000 in
theorem selected_zeroPolynomial_J2
    (i : Fin (m+1)) (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (hzero : coreA T (fun _ => false)=true) :
    let c := physicalRootCall f ell base m l q T w
    let sel := exactJ6Selector (f:=f) (ell:=ell) base m l q native T w mask hm hL hn
    let t := oddRootCenter f ell base m l q native T w hn i
    let p := registerPrecision (rootParams f ell m native) c t
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    let Z := plantedScalar m l q T w mask hm hL i
    (J6R14ZeroMode.physicalZeroP sel d t hf).eval 0 =
        J6ZeroTransport.reduceAt p (box_two_nil p f ell) Z ∧
      twoLocalRat Z =
        J6Recovery.layerSum m q (J6IntegerLayers.oldWeight (coreA T))
          (J6IntegerLayers.oldWeight (coreB T)) (J6PhysicalInteger.loads m l mask w hm hL) i := by
  exact ⟨selected_zeroPolynomial_at_odd base m l q native T w mask hm hL hn d i hf hbase hF hℓ,
    plantedScalar_J2 m l q T w mask hm hL hzero i⟩

#print axioms selected_zeroPolynomial_at_odd
#print axioms selected_zeroPolynomial_J2
end
end J6R15PlantedIdentity
