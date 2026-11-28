import J6R14ZeroModeRun
import J6R14ZeroModeDegree
import J6R14ZeroModeProbe

/-! Exact fallback J6, lines 2026--2037: interpolate one fixed zero-mode
polynomial from prescribed, nonzero binary words. No grouped sample over
beta occurs in the outer table; its cells are products of actual runs. -/
namespace J6R14ZeroMode
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R12Blueprint J6R11Blueprint J6R10Repack J6R12Repack J1PPrinted
noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) (t : Center (printedParams (f:=f) (ell:=ell) s) c)

def physicalZeroP (hf : f.Monic) : (Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t))[X] :=
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  polynomial (packing sel d) (centerIndex d t) t.val (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) c.host.file hf

theorem physicalZeroP_degree (hf : f.Monic) : (physicalZeroP sel d t hf).natDegree ≤ (J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth)) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have h := degree (packing sel d) (centerIndex d t) t.val (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
    (active_grid _ _ _ t.property).1 c.host.file hf
  change (physicalZeroP sel d t hf).natDegree ≤
    J9PrintedSchedule.degreeBound c.host.edgeCount (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth) at h
  rwa [d.edgeCount] at h

theorem physicalZeroP_eval (cfg : RootBounds s C f) (seed : Stable s C c)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (z : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)) : (physicalZeroP sel d t hf).eval z = zeroRuntime sel d t hf z := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  refine (polynomial_eval (packing sel d) (centerIndex d t) (centerNonzero t)
    rfl (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) c.host.file hf z).trans ?_
  unfold zeroRuntime
  exact Finset.prod_congr rfl (fun g _ => (zeroChildRun_exact sel d t cfg seed hf hF z g).symm)

def fallbackTable (hf : f.Monic) (W : Prescribed f (J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth))) (j : Fin ((J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth))+1)) : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  zeroRuntime sel d t hf (prescribedNode W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell j)

def fallback (hf : f.Monic) (W : Prescribed f (J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth))) : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  (J6ActiveInterpolation.decoded (prescribedNode W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell) (fallbackTable sel d t hf W)).eval 0

theorem interpolate_zeroMode (cfg : RootBounds s C f) (seed : Stable s C c)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Prescribed f (J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth))) :
    J6ActiveInterpolation.decoded (prescribedNode W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell) (fallbackTable sel d t hf W) =
      physicalZeroP sel d t hf := by
  have ht : fallbackTable sel d t hf W =
      (fun j => (physicalZeroP sel d t hf).eval (prescribedNode W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell j)) :=
    funext (fun j => (physicalZeroP_eval sel d t cfg seed hf hF (prescribedNode W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell j)).symm)
  rw [ht]
  exact J6ActiveInterpolation.decoded_exact _ _ (physicalZeroP_degree sel d t hf)
    (prescribed_units W (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) ell (J6R12Blueprint.register_positive d t) hf hF)

/-- RHS is the *reference value* at the omitted probe. Its actual run is
not made to construct the fallback table on the left. -/
theorem fallback_exact (cfg : RootBounds s C f) (seed : Stable s C c)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (W : Prescribed f (J9PrintedSchedule.degreeBound c.edges (2^(printedParams (f:=f) (ell:=ell) s).levelBits c.depth))) :
    fallback sel d t hf W = zeroRuntime sel d t hf 0 := by
  rw [fallback,interpolate_zeroMode sel d t cfg seed hf hF W]
  exact physicalZeroP_eval sel d t cfg seed hf hF 0

theorem root_table_cells (k M L : ℕ) :
    Nat.card (Fin k × Fin (J9PrintedSchedule.probeCount M L)) = k*(M*(2*L-1)+1) := by
  rw [Nat.card_prod,Nat.card_fin,Nat.card_fin]
  rfl

theorem root_child_addresses (k M L : ℕ) :
    Nat.card (Fin k × Fin (J9PrintedSchedule.probeCount M L) × Fin 64) =
      k*((M*(2*L-1)+1)*64) := by
  rw [Nat.card_prod,Nat.card_prod,Nat.card_fin,Nat.card_fin,Nat.card_fin]
  rfl

#print axioms physicalZeroP_degree
#print axioms physicalZeroP_eval
#print axioms fallbackTable
#print axioms interpolate_zeroMode
#print axioms fallback_exact
#print axioms root_table_cells
#print axioms root_child_addresses
end
end J6R14ZeroMode
