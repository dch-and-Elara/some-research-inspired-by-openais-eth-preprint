import J6R12IntegralClosedCore
import J6R12BlueprintReach
import J1PPrintedSize

/-! Instantiate the all-active semantic result with the verified
printed size, degree and creation-tag invariant, at every physically
generated call. Only the explicit initial hypotheses remain. -/
namespace J6R12Integral
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint J6R11Blueprint J1PPrinted

variable {f : ℤ[X]} {ell : ℕ} {s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell))
local notation "S₀" => (printedParams (f:=f) (ell:=ell) s)
local notation "Δ₀" => sourceDelta s

def printedGuards (seed : Stable s C r) : NativeGuards S₀ Δ₀ sel r where
  ready := fun c hc ha => ready_reachable cfg sel hc seed ha
  taper := by
    intro c hc ha
    have h := stable_reachable cfg sel hc seed
    have hh := printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size ha
      h.sizeByDepth
    exact ⟨hh.1,hh.2.2⟩

variable [envDec : DecidableEq (Envelope (shape S₀ Δ₀ sel) (children S₀ Δ₀ sel) r)]

omit envDec in
include cfg in
theorem printed_run_exact (seed : Stable s C r) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    (J6R12Blueprint.sourceBlueprint sel r hf).program.run r =
      reduce r.prec f ell (r.host.contract hf) :=
  native_run_root S₀ Δ₀ sel r (printedGuards cfg sel r seed) hf hF seed.edgeCount

#print axioms printedGuards
#print axioms printed_run_exact
end J6R12Integral
