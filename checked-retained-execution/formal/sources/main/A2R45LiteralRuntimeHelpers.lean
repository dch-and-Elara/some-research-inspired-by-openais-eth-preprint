
import J6R14ZeroModeFallback
import J6R12RepackReadNatural

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
set_option maxRecDepth 1900
set_option linter.unusedSectionVars false

/-! Abstract only in the actual source call, so concrete padded sizes
do not get normalized during elaboration of dependent receiver types. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R11Blueprint J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R12Blueprint J6R12Repack J1PPrinted

noncomputable section
variable {f : ℤ[X]} {s C : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=1) s) (sourceDelta s))
variable {c : Call (PhysicalHost f 1)}
variable (d : Ready (printedParams (f:=f) (ell:=1) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=1) s) c)
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "p" => registerPrecision S c t
variable (hf : f.Monic)

def zeroValue (v : ℕ) : Prop :=
  (J6R14ZeroMode.physicalZeroP sel d t hf).eval 0 = (v:Box f 1 p)

def completedRead (word : Fin f.natDegree→Bool) : ℕ :=
  boxNatural f 1 p hf
    (J6R14ZeroMode.zeroRuntime sel d t hf
      (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f word)))

def zeroRead : ℕ := completedRead sel d t hf (fun _=>false)

def recoverRead (bank : J6R14ZeroMode.Prescribed f
    (J9PrintedSchedule.degreeBound c.edges (2^((S).levelBits c.depth)))) : ℕ :=
  boxNatural f 1 p hf (J6R14ZeroMode.fallback sel d t hf bank)

theorem binary_zero_probe (p' : ℕ) :
    J6ActiveInterpolation.scalarIn p' f 1 (NativeProbeRing.probe p' f (fun _=>false))=0 := by
  rw [J6R14ZeroMode.actual_probe_zero,map_zero]

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
theorem zeroRead_exact (cfg : RootBounds s C f) (seed : Stable s C c)
    (hF : 0<f.natDegree) (v : ℕ) (fit : v<2^p)
    (truth : zeroValue sel d t hf v) :
    zeroRead sel d t hf=v := by
  unfold zeroRead completedRead
  rw [binary_zero_probe (f:=f) p,←J6R14ZeroMode.physicalZeroP_eval sel d t cfg seed hf hF 0]
  rw [zeroValue] at truth
  rw [truth]
  exact boxNatural_of_nat f 1 p hf (register_positive d t) (by decide) hF v fit

theorem recoverRead_eq_zeroRead (cfg : RootBounds s C f) (seed : Stable s C c)
    (hF : 0<f.natDegree)
    (bank : J6R14ZeroMode.Prescribed f
      (J9PrintedSchedule.degreeBound c.edges (2^((S).levelBits c.depth)))) :
    recoverRead sel d t hf bank=zeroRead sel d t hf := by
  unfold recoverRead zeroRead completedRead
  rw [binary_zero_probe (f:=f) p,J6R14ZeroMode.fallback_exact sel d t cfg seed hf hF bank]

#print axioms zeroValue
#print axioms completedRead
#print axioms zeroRead_exact
#print axioms recoverRead_eq_zeroRead
end
end A2R45Literal
