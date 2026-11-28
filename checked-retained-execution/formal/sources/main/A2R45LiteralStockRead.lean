
import A2R45LiteralStockCalls
import A2R45LiteralRuntimeHelpers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000
set_option maxRecDepth 2000
set_option linter.unusedSectionVars false

/-! Turn the actual installed agenda into the exact single-mode
oracle or the exact same-mode interpolation table. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R11Blueprint J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R12Blueprint J6R12Repack J1PPrinted

noncomputable section
variable {f : ℤ[X]} {s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=1) s) (sourceDelta s))
variable {c : Call (PhysicalHost f 1)}
variable (d : Ready (printedParams (f:=f) (ell:=1) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=1) s) c)
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "p" => registerPrecision S c t
variable (hf : f.Monic)

def installedRead (z : Probe S c) : ℕ :=
  boxNatural f 1 p hf (installedZeroProduct sel d t hf z)

theorem installedRead_is_binary_read (z : Probe S c) :
    installedRead sel d t hf z=completedRead sel d t hf (stockWord d z) := by
  unfold installedRead completedRead
  rw [installedZeroProduct_eq,sampleNode_is_stockWord]

def installedInterpolationRead : ℕ :=
  boxNatural f 1 p hf
    ((J6ActiveInterpolation.decoded (sampleNode S f 1 c d.fit t)
      (installedZeroProduct sel d t hf)).eval 0)

theorem installedInterpolationRead_is_same_mode
    (hmiss : ∀ z,stockWord d z≠fun _=>false) :
    installedInterpolationRead sel d t hf=
      recoverRead sel d t hf (stockRosterNoZero d hmiss) := by
  unfold installedInterpolationRead recoverRead J6R14ZeroMode.fallback
  rw [installedZeroProductTable sel d t hf hmiss]
  rfl

#print axioms installedRead_is_binary_read
#print axioms installedInterpolationRead_is_same_mode
end
end A2R45Literal
