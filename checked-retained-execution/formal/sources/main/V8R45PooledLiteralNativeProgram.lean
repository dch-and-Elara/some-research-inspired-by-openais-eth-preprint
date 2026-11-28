import J6R12IntegralDirectPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
set_option maxRecDepth 1800

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial J6R12Blueprint J6R11Blueprint J6R9Recursive J6R10Repack J6ActiveRun
noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ}

def nativePrintedRun
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s))
    (c : Call (PhysicalHost f ell)) (hf : f.Monic) : Box f ell c.prec :=
  (J6R12Blueprint.sourceBlueprint sel c hf).program.run c

theorem native_printed_run_exact
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s))
    (c : Call (PhysicalHost f ell)) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (cfg : RootBounds s C f) (stable : Stable s C c) :
    nativePrintedRun sel c hf = reduce c.prec f ell (c.host.contract hf) := by
  unfold nativePrintedRun
  exact J6R12Integral.printed_run_exact cfg sel c stable hf hd

#print axioms nativePrintedRun
#print axioms native_printed_run_exact
end
end V8R45PooledLiteral