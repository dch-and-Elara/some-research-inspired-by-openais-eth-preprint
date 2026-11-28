
import J6R26StablePreparedRootProbe
import J6R26StablePreparedRootInterpolate

/-! Produce the actual completed fixed-zero-mode ring register from the
nonzero outer probes and the separately prepared true native subtrees.
The omitted zero probe is not executed. -/
namespace J6R26StablePreparedRoot
open scoped Polynomial BigOperators
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R22Active J6R14ZeroMode
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
set_option maxRecDepth 1500

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {c : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "D" => externalProbeDegree s c

noncomputable def ProbeJob.completedWords
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) (hv : 0<ell)
    (read : Fin (D+1)→Meter {x : List Bool //x.length=J.frame.words.length}) :
    Meter (Block J.frame ell) :=
  interpolateAt0 J.frame.hp J.frame.sizePos hv (readPrescribed J.frame.hp hv read) (J.sampleWords hv)

theorem ProbeJob.completed_exact
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) (hv : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (seed : Stable s C c)
    (read : Fin (D+1)→Meter {x : List Bool //x.length=J.frame.words.length})
    (raw : ∀ j,(read j).result.val=List.ofFn (J.W.word j)) :
    let p := registerPrecision S c J.centre
    let out := J.completedWords hv read
    J.frame.decode out.result=(@physicalZeroP f ell s sel c J.ready J.centre hf).eval 0 ∧
    out.steps ≤ interpBill (readPrescribed J.frame.hp hv read) (J.sampleWords hv)+
      interpExtra J.frame.words.length ell p 1 (D+1) J.frame.hp+jetCoeffFee J.frame.words.length ell p 1+3 := by
  let p := registerPrecision S c J.centre
  let F := J.frame
  let P := @physicalZeroP f ell s sel c J.ready J.centre hf
  have hD := F.natDegree hf
  have hF : 0<f.natDegree := hD ▸ F.sizePos
  have nodes (j : Fin (D+1)) :=
    (read_prescribed_exact F.hp hv J.W F.exactMod read raw j).1
  have samples (j : Fin (D+1)) :
      boxTransport F.exactMod (nodeMeaning F.hp (J.sampleWords hv) j) =
        P.eval (prescribedNode J.W p ell j) :=
    (J.sample_exact hv j).1.trans
      (physicalZeroP_eval (f:=f) (ell:=ell) (s:=s) (C:=C) (c:=c) sel J.ready J.centre
        cfg seed hf hF (prescribedNode J.W p ell j)).symm
  exact prescribed_interpolate_at_zero F.hp F.sizePos hv hf hF hD F.exactMod J.W _ _ P
    (@physicalZeroP_degree f ell s sel c J.ready J.centre hf) nodes samples

#print axioms ProbeJob.completed_exact
end J6R26StablePreparedRoot
