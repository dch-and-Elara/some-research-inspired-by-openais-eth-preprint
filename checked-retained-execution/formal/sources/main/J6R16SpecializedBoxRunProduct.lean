import J6R16SpecializedBoxRun

/-! A reducible name for the checked product of honest recursive child
programs. Its type fixes the parent address before the concrete
orientation is instantiated. -/
namespace J6R14SpecializedBox
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6R12Blueprint J6R11Blueprint J6R12Integral
open J1PPrinted J9R15FrozenErasurePhysical
noncomputable section
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell s C : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
variable (z : Probe (printedParams (f:=f) (ell:=ell) s) c)
variable (β : LiteralMenu sel d t)
variable (hf : f.Monic)

def printedPacketProduct : Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  ∏ g : Fin 64, (sourceBlueprint sel (samePacketCall (s:=s) (c:=c) sel d t z β g) hf).program.run
    (samePacketCall (s:=s) (c:=c) sel d t z β g)

theorem printedPacketProduct_exact (cfg : RootBounds s C f) (seed : Stable s C c)
    (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    printedPacketProduct sel d t z β hf =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       actualProjection (packing sel d) (centerIndex d t) (centerNonzero t) rfl
         (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
         (sampleNode (printedParams (f:=f) (ell:=ell) s) f ell c d.fit t z) c.host.file hf β.val) :=
  recursively_evaluated_fixed_actual_product cfg sel d t z β seed hf hF

#print axioms printedPacketProduct_exact
end
end J6R14SpecializedBox