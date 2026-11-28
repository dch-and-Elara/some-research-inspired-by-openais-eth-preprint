import V8R45PooledLiteralDispatch
import V8R45PooledLiteralNativeProgram

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2100000
set_option maxRecDepth 2200

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R10Repack J6R9Recursive J6R11Blueprint J6R12Blueprint

noncomputable section

private theorem cast_receive_exact (f : ℤ[X]) {p q : ℕ} (h : p=q) (x : IntRing f 1) :
    cast (congrArg (Residue f 1) h) (reduce p f 1 x) = reduce q f 1 x := by
  cases h
  rfl

variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)

/-- Recurse on the newly produced host with the exact source semantics.
The transport is equality of precision indices, not any precision loss. -/
def exteriorRun (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V))
       (J1PPrinted.sourceDelta (rootSize V)))
    (W : Probes V f) (hf : f.Monic) (s : V → Bool) (t : Site V)
    (q : Address P hu huM t) (g : Fin 64) : Residue f 1 (high t) :=
  cast (congrArg (Residue f 1) (exterior_child_return_precision P hu huM W s t q g))
    (@nativePrintedRun f 1 (rootSize V) sel (exteriorChild P hu huM W s t q g) hf)

theorem exterior_run_exact_receives
    (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V))
       (J1PPrinted.sourceDelta (rootSize V)))
    (W : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    [F : Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (s : V → Bool) (t : Site V) (q : Address P hu huM t) (g : Fin 64)
    (cfg : RootBounds (rootSize V) 3 f)
    (stable : Stable (rootSize V) 3 (exteriorChild P hu huM W s t q g)) :
    exteriorRun P hu huM sel W hf s t q g =
      reduce (high t) f 1 ((exteriorChild P hu huM W s t q g).host.contract hf) := by
  unfold exteriorRun
  rw [@native_printed_run_exact f 1 (rootSize V) 3 sel _ hf hd F cfg stable]
  exact cast_receive_exact f (exterior_child_return_precision P hu huM W s t q g) _

#print axioms exteriorRun
#print axioms exterior_run_exact_receives
end
end V8R45PooledLiteral