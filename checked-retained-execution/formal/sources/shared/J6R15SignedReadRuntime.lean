import J6R15SignedReadAcquired
import J6R15PlantedIdentityCenter

/-! Final guard-preserving composition: actual outer beta=0 product,
raw signed J2 scalar, exactly centered receiver, signed integer odd
root and rational interpolation back to the original CNF count. -/
namespace J6R15SignedRead
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P1DyadicGrid J6Mesh J6OrientedHost J6R9Recursive
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Integral J6R10Integral
open J6R12Repack J6R14ZeroMode J6R12Blueprint J6R11Blueprint J1PPrinted
open J6RepairedCentered J6NativeHeightResidue J6OrientedHostEval
set_option maxHeartbeats 7800000

theorem castBox_reduceAt (f : ℤ[X]) (ell : ℕ) {p q : ℕ} (h : p=q)
    (x : DenominatorBudget.TwoLocal) :
    castBox f ell h (J6ZeroTransport.reduceAt p (box_two_nil p f ell) x) =
      J6ZeroTransport.reduceAt q (box_two_nil q f ell) x := by
  subst q
  rfl

theorem runtime_at_parent
    {f : ℤ[X]} {ell s C : ℕ} {c : Call (PhysicalHost f ell)}
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c)
    (cfg : RootBounds s C f) (seed : Stable s C c)
    (hf : f.Monic) (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    zeroRuntime sel d t hf 0 = ((parentJet (packing sel d) c.host.file hf t.val).map
      (reduce p f ell)).eval 0 := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
  have ht := active_grid _ _ _ t.property
  refine (physicalZeroP_eval sel d t cfg seed hf hF 0).symm.trans ?_
  change (polynomial (packing sel d) (centerIndex d t) t.val p c.host.file hf).eval 0 = _
  exact J6R15PlantedIdentity.zero_eq_parentJet (packing sel d) (centerIndex d t)
    ht.1 ht.2 rfl p (J6R12Blueprint.register_positive d t) c.host.file hf

#print axioms castBox_reduceAt
#print axioms runtime_at_parent
end J6R15SignedRead