import J6R53PublicMountReadout
import J6R52FreshShapeValue

/-! Separate fresh-plant specialization: removes final arithmetic
opening/cardinality premises on exactly the submitted fresh chart.
It does not construct the mounted group family from a raw CNF. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame J6R22RootReadout
open J6R51Ingress J6R52FreshShape J7R9Compiler J7R9Subdivision J7R10Plant
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 6800000
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
attribute [local irreducible] runMountedCount
noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (C : CNF V) (order : DeclaredOrder V)
local notation "graphF" => (guardedInOrder C order.roster)
local notation "plantF" => (freshPlant graphF (guardRoster order))
local notation "mF" => (nWires graphF)
local notation "nF" => (nSubdiv graphF)
local notation "vF" => (OrderedOld graphF)
variable {f : ℤ[X]} {base native ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable (G : RootShape f (nWires (guardedInOrder C order.roster))
  (printedHalf (nWires (guardedInOrder C order.roster))) base native
  (printedRankWidth (nWires (guardedInOrder C order.roster)))
  (freshPlant (guardedInOrder C order.roster) (guardRoster order))
  (constantRootWord (nWires (guardedInOrder C order.roster))))
variable (hf : f.Monic)
variable (frame : Frame f (J6SourcePrecision.printed (nWires (guardedInOrder C order.roster)) base))
variable (hv : 0<ell)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (groups : MountedFamily (V:=OrderedOld (guardedInOrder C order.roster)) (f:=f)
  (m:=nWires (guardedInOrder C order.roster)) (n:=nSubdiv (guardedInOrder C order.roster))
  (base:=base) (native:=native) (T:=freshPlant (guardedInOrder C order.roster) (guardRoster order))
  G ell q rr cc dd edgew tc tj key prec tw bw rate pad)

def freshCountMeter : Meter (A1R10.Word (printedAnswerWidth mF base)) :=
  runMountedCount (V:=vF) (f:=f) (m:=mF) (n:=nF) (base:=base) (native:=native)
    (T:=plantF) (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew)
    (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad) G hf frame hv groups

theorem fresh_mounted_public_count_word (positiveBase : 0<base) :
    bitsValue (freshCountMeter C order G hf frame hv groups).result.val=PinnedCNF.modelCount C := by
  have opener : coreA plantF (fun _=>false)=true := (actual_fresh_zero_opening C order).1
  have cnt : Nat.card {x : Fin mF→Bool // coreA plantF x=true ∧ coreB plantF x=true} =
    1+PinnedCNF.modelCount C := fresh_submitted_CNF_count C order (guardRoster order)
  have H := actual_mounted_public_count (V:=vF) (f:=f) (m:=mF) (n:=nF) (base:=base) (native:=native)
    (T:=plantF) (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew)
    (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad)
    G hf frame hv groups positiveBase opener (PinnedCNF.modelCount C) cnt
  exact H.1

#print axioms fresh_mounted_public_count_word
end
end J6R53PublicMount
