
import J6R26StablePreparedRootAdapter
import J6R26StablePreparedRootFrame
import J6R26StablePreparedRootCalls

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
set_option maxHeartbeats 1100000
set_option maxRecDepth 2000




theorem external_zero_precision {f : ℤ[X]} {ell s : ℕ}
    (sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s))
    {c : Call (PhysicalHost f ell)}
    (d : Ready (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s) c)
    (t : Center (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c)
    (W : Prescribed f (externalProbeDegree s c)) (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) :
    (@externalZeroCall f ell s sel c d t W j g).prec=
      registerPrecision (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c t := rfl


/-- This is only the supplied physical descriptor family, not a table
of responses. Every child slot has the literal native zero-child type. -/
structure ProbeJob (f : ℤ[X]) (ell s C : ℕ) (cfg : RootBounds s C f)
    (sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s))
    (c : Call (PhysicalHost f ell)) (hf : f.Monic) where
  ready : Ready (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s) c
  centre : Center (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c
  W : Prescribed f (externalProbeDegree s c)
  frame : Frame f (registerPrecision (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c centre)
  run : ∀ (j : Fin (externalProbeDegree s c+1)) (g : Fin 64),
    @ProbePrepared f ell s C cfg hf sel c ready centre W j g

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {c : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable def ProbeJob.groupWords
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) :
    Meter (Block J.frame ell) :=
  let k := @externalZeroCall f ell s sel c J.ready J.centre J.W j g
  let e := @external_zero_precision f ell s sel c J.ready J.centre J.W j g
  let shadow := siteFrame e J.frame
  let raw := @preparedOnFrame f ell s C cfg k hf sel (J.run j g) shadow
  restoreFrame e J.frame raw

theorem ProbeJob.group_exact
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) :
    J.frame.decode (J.groupWords j g).result =
      @J6R14ZeroMode.zeroChildRun f ell s sel c J.ready J.centre hf
        (prescribedNode J.W (registerPrecision S c J.centre) ell j) g := by
  let k := @externalZeroCall f ell s sel c J.ready J.centre J.W j g
  let e := @external_zero_precision f ell s sel c J.ready J.centre J.W j g
  let shadow := siteFrame e J.frame
  let raw := @preparedOnFrame f ell s C cfg k hf sel (J.run j g) shadow
  have h := (@prepared_on_frame_exact f ell s C cfg k hf sel (J.run j g) shadow _).1
  change J.frame.decode (restoreFrame e J.frame raw).result=_
  rw [(restore_frame_receipt e J.frame raw).1,h]
  rfl

noncomputable def ProbeJob.sampleWords
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) (hv : 0<ell) (j : Fin (externalProbeDegree s c+1)) :
    Meter (Block J.frame ell) :=
  foldM J.frame.hp J.frame.sizePos hv (J.groupWords j) (groupOrder 64)

theorem ProbeJob.sample_exact
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    (J : ProbeJob f ell s C cfg sel c hf) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hv : 0<ell) (j : Fin (externalProbeDegree s c+1)) :
    let p := registerPrecision S c J.centre
    let out := J.sampleWords hv j
    J.frame.decode out.result=
      @J6R14ZeroMode.zeroRuntime f ell s sel c J.ready J.centre hf (prescribedNode J.W p ell j) ∧
    out.steps ≤ bill (J.groupWords j) (groupOrder 64)+tupleExtra J.frame.words.length ell p 64 := by
  let p := registerPrecision S c J.centre
  let F := J.frame
  let value := J.groupWords j
  refine ⟨?_,?_⟩
  · change boxTransport F.exactMod (uvRead F.hp F.words ell
      (foldM F.hp F.sizePos hv value (groupOrder 64)).result)=_
    rw [prodM_value,groupOrder,List.map_ofFn,List.prod_ofFn,map_prod,zeroRuntime]
    exact Finset.prod_congr rfl (fun g _=>J.group_exact j g)
  · have cost := (prodM_steps F.hp F.sizePos hv value (groupOrder 64)).2
    simpa only [ProbeJob.sampleWords,groupOrder,List.length_ofFn,tupleExtra,Nat.add_assoc] using cost

#print axioms external_zero_precision
#print axioms ProbeJob.group_exact
#print axioms ProbeJob.sample_exact
end J6R26StablePreparedRoot
