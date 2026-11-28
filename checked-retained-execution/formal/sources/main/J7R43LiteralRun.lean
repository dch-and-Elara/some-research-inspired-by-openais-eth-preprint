import J6R16SpecializedBoxRun

/-! A single real recursive physical child, at its own receiving
precision. No product over other groups is formed. -/
namespace J7R43Literal
open scoped Polynomial BigOperators Classical
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint J6R11Blueprint
open J1PPrinted J6R12Integral J6R11Integral J6R10Repack
open J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {f : ℤ[X]} {ell : ℕ} {s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable (t : Center (printedParams (f:=f) (ell:=ell) s) c)
variable (z : Probe (printedParams (f:=f) (ell:=ell) s) c)
variable (β : LiteralMenu sel d t) (g : Fin 64)

def printedPacketValue (hf : f.Monic) :
    Box f ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) :=
  (sourceBlueprint sel (samePacketCall (s:=s) (c:=c) sel d t z β g) hf).program.run
    (samePacketCall (s:=s) (c:=c) sel d t z β g)

set_option maxHeartbeats 4000000 in
include cfg in
theorem run_one_actual_child
    (seed : Stable s C c) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    printedPacketValue (s:=s) (c:=c) sel d t z β g hf =
      (letI := c.host.finiteEdge
       letI := c.host.finiteRow
       letI := c.host.finiteCol
       reduce (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) f ell
        (actualChildTruth (packing sel d) (centerIndex d t) (centerNonzero t) rfl
          (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
          (sampleNode (printedParams (f:=f) (ell:=ell) s) f ell c d.fit t z) c.host.file hf β.val g)) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  unfold printedPacketValue
  rw [printed_run_exact cfg sel _ (samePacketCall_stable cfg sel d t z β g seed) hf hF]
  exact congrArg _ (packetOfSite_truth sel d t z β.val g hf)

#print axioms printedPacketValue
#print axioms run_one_actual_child
end
end J7R43Literal