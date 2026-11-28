
import A2R45LiteralStockAddress
import J6R14ZeroModeFallback

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option synthInstance.maxHeartbeats 250000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! Product oracle at existing Appendix D probe addresses, not at
invented probes. The dependent runs keep their actual creation tags
and homing register precision. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R12Blueprint J6R11Blueprint J6R11Repack J1PPrinted

noncomputable section
variable {f : ℤ[X]} {s : ℕ} (sel : Selector (printedParams (f:=f) (ell:=1) s) (sourceDelta s))
variable {c : Call (PhysicalHost f 1)}
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "P" => nativePlan (shape S Δ sel) (children S Δ sel)
variable (d : Ready (printedParams (f:=f) (ell:=1) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=1) s) c)

def stockDestination (z : Probe S c) (g : Fin 64) : Call (PhysicalHost f 1) :=
  (P).child c ⟨stockAddress sel d t z g,d.active⟩

def stockChildCall (hf : f.Monic) (z : Probe S c) (g : Fin 64) :
    Box f 1 (registerPrecision S c t) :=
  let u := stockDestination sel d t z g
  (J6R12Blueprint.sourceBlueprint sel u hf).program.run u

theorem stockChildCall_eq (hf : f.Monic) (z : Probe S c) (g : Fin 64) :
    stockChildCall sel d t hf z g =
      @J6R14ZeroMode.zeroChildRun f 1 s sel c d t hf (sampleNode S f 1 c d.fit t z) g := by
  let encode (u : Call (PhysicalHost f 1)) : Σ p : ℕ, Box f 1 p :=
    ⟨u.prec,(J6R12Blueprint.sourceBlueprint sel u hf).program.run u⟩
  have eq := congrArg encode (stock_child_is_packet sel d t z g)
  exact eq_of_heq (Sigma.mk.inj_iff.mp eq).2

def installedZeroProduct (hf : f.Monic) (z : Probe S c) :
    Box f 1 (registerPrecision S c t) :=
  ∏ g : Fin 64,stockChildCall sel d t hf z g

theorem installedZeroProduct_eq (hf : f.Monic) (z : Probe S c) :
    installedZeroProduct sel d t hf z =
      @J6R14ZeroMode.zeroRuntime f 1 s sel c d t hf (sampleNode S f 1 c d.fit t z) := by
  unfold installedZeroProduct J6R14ZeroMode.zeroRuntime
  exact Finset.prod_congr rfl (fun g _=>stockChildCall_eq sel d t hf z g)

def stockWord (z : Probe S c) : Fin f.natDegree→Bool :=
  NativeProbeRing.chosenRep f.natDegree _ d.fit z

theorem sampleNode_is_stockWord (z : Probe S c) :
    sampleNode S f 1 c d.fit t z =
      J6ActiveInterpolation.scalarIn (registerPrecision S c t) f 1
        (NativeProbeRing.probe (registerPrecision S c t) f (stockWord d z)) := rfl

def stockRosterNoZero (h : ∀ z,stockWord d z≠fun _=>false) :
    J6R14ZeroMode.Prescribed f (J9PrintedSchedule.degreeBound c.edges (2^((S).levelBits c.depth))) where
  word := stockWord d
  distinct := NativeProbeRing.chosenRep_injective _ _ d.fit
  excludesZero := h

theorem installedZeroProductTable (hf : f.Monic)
    (h : ∀ z,stockWord d z≠fun _=>false) :
    installedZeroProduct sel d t hf =
      @J6R14ZeroMode.fallbackTable f 1 s sel c d t hf (stockRosterNoZero d h) := by
  funext z
  exact installedZeroProduct_eq sel d t hf z

#print axioms stockDestination
#print axioms stockChildCall_eq
#print axioms installedZeroProduct_eq
#print axioms sampleNode_is_stockWord
#print axioms stockRosterNoZero
#print axioms installedZeroProductTable
end
end A2R45Literal
