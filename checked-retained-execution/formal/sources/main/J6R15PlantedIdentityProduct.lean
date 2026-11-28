import J6R15PlantedIdentityRational

/-! Exact printed product in characteristic zero for the same localized sample. -/
namespace J6R15PlantedIdentity
open scoped Classical Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval
noncomputable section

variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V]

theorem plantedScalar_J2_product
    (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (mask : MaskFamily (a m) (K m) S)
    (hm : m ≤ K m) (hL : 2*l=L m) (hzero : coreA T (fun _ => false)=true)
    (i : Fin (m+1)) :
    letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
    let n := J6PhysicalInteger.loads m l mask w hm hL
    let A := J6IntegerLayers.oldWeight (coreA T)
    let B := J6IntegerLayers.oldWeight (coreB T)
    twoLocalRat (plantedScalar m l q T w mask hm hL i) =
      J6Recovery.publicFactor m q n i *
        ((LayerRecovery.layerPolynomial A B).eval (point m i)) ^ J6Recovery.exp m i := by
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  exact (plantedScalar_J2 m l q T w mask hm hL hzero i).trans
    (J6Recovery.layerSum_factorization m q (J6IntegerLayers.oldWeight (coreA T))
      (J6IntegerLayers.oldWeight (coreB T)) (J6PhysicalInteger.loads m l mask w hm hL) i)

#print axioms plantedScalar_J2_product
end
end J6R15PlantedIdentity
