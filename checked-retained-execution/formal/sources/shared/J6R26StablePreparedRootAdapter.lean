
import J6R14ZeroModeFallback
import J6R24MeteredRecursionWhole

/-! Use an actual measured Prepared run of each external zero-mode
child. These externally prescribed words need not be a native-prefix
probe of the parent. Their children nevertheless run the same fixed
selector and printed recursion on exactly the physical calls they
compile to. A checked, charged frame copy is the only adaptation. -/
namespace J6R26StablePreparedRoot
open scoped Classical Polynomial BigOperators
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R21Ancestor
open J6R24MeteredRecursion J6R19Retained J6R18ChildWrite J6R22Active
open J6R14ZeroMode
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000
set_option maxRecDepth 2000

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {c : Call (PhysicalHost f ell)} {hf : f.Monic}

noncomputable def preparedOnFrame
    {selection : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (T : @J6R24MeteredRecursion.Prepared f ell s C cfg selection c hf) (F : Frame f c.prec) :
    Meter (Block F ell) := by
  let hi : NativeReach (Plan selection) c c := NativeReach.reflexive c
  let raw : Meter (Block (T.frame hi) ell) := Prepared.run T c hi
  let E : (T.frame hi).words.length=F.words.length :=
    ((T.frame hi).natDegree hf).trans ((F.natDegree hf).symm)
  let res : Meter (Block F ell) := J6R19Retained.resizeUV (new:=F.words) E raw.result
  exact ⟨res.result,raw.steps+res.steps+4⟩

theorem prepared_on_frame_exact
    {selection : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (T : @J6R24MeteredRecursion.Prepared f ell s C cfg selection c hf) (F : Frame f c.prec)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let hi : NativeReach (Plan selection) c c := .reflexive c
    let result := preparedOnFrame T F
    F.decode result.result=(sourceBlueprint selection c hf).program.run c ∧
    (T.run c hi).steps≤result.steps ∧
    result.steps≤(T.run c hi).steps+boxFee f.natDegree ell c.prec c.prec+4 := by
  let hi : NativeReach (Plan selection) c c := .reflexive c
  let V := T.frame hi
  let raw := T.run c hi
  let Q : Meter (Block F ell) := resizeUV ((V.natDegree hf).trans (F.natDegree hf).symm) raw.result
  have hE : 0<f.natDegree := V.natDegree hf ▸ V.sizePos
  have native := native_resizeUV V.hp F.hp hf hE V.exactMod F.exactMod raw.result
  have recurse := T.correctAt c hi
  refine ⟨?_,?_,?_⟩
  · have step : F.decode Q.result=V.decode raw.result := by
      change boxTransport F.exactMod (uvRead F.hp F.words ell Q.result)=
        boxTransport V.exactMod (uvRead V.hp V.words ell raw.result)
      rw [boxTransport_cast F.exactMod,native.1,boxTransport_cast V.exactMod]
      exact canonicalLift_spec c.prec f hf ell _
    exact step.trans recurse
  · change raw.steps≤raw.steps+Q.steps+4
    omega
  · change raw.steps+Q.steps+4≤raw.steps+boxFee f.natDegree ell c.prec c.prec+4
    exact Nat.add_le_add_right (Nat.add_le_add_left native.2 _) _

#print axioms prepared_on_frame_exact
end J6R26StablePreparedRoot
