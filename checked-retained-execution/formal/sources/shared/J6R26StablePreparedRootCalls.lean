
import J6R14ZeroModeFallback
import J6R24MeteredRecursionRun

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
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000


abbrev externalProbeDegree {f : ℤ[X]} {ell : ℕ} (s : ℕ) (c : Call (PhysicalHost f ell)) : ℕ :=
  J9PrintedSchedule.degreeBound c.edges
    (2^(Shape.levelBits (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c.depth))

noncomputable def externalZeroCall {f : ℤ[X]} {ell s : ℕ}
    (sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s))
    {c : Call (PhysicalHost f ell)}
    (d : Ready (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s) c)
    (t : Center (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c)
    (W : Prescribed f (externalProbeDegree s c)) (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) :
    Call (PhysicalHost f ell) :=
  @J6R14ZeroMode.zeroChild f ell s sel c d t
    (@prescribedNode f (externalProbeDegree s c) W
      (registerPrecision (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c t) ell j) g

/-- The root of each real prepared subtree is precisely the physical
zero child at this requested prescribed word and actual subgroup. -/
noncomputable abbrev ProbePrepared {f : ℤ[X]} {ell s C : ℕ}
    {cfg : RootBounds s C f} {hf : f.Monic}
    {sel : J6R12Blueprint.Selector (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s)}
    {c : Call (PhysicalHost f ell)}
    (d : Ready (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) (J1PPrinted.sourceDelta s) c)
    (t : Center (J6R12Blueprint.printedParams (f:=f) (ell:=ell) s) c)
    (W : Prescribed f (externalProbeDegree s c)) (j : Fin (externalProbeDegree s c+1)) (g : Fin 64) : Type 1 :=
  @J6R24MeteredRecursion.Prepared f ell s C cfg sel (@externalZeroCall f ell s sel c d t W j g) hf

#print axioms externalZeroCall
#print axioms ProbePrepared
end J6R26StablePreparedRoot
