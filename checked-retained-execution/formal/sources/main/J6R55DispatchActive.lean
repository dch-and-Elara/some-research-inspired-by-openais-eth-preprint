import J6R55DispatchProbeMeter
import J6R49DFSActive

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 3300
set_option Elab.async false

/-! Same active stage with live raw-mode callback arguments. Every
centre, jet, probe and output frame comes from the original machine.
No independent interpolation table or caller-supplied arithmetic. -/
namespace J6R55Dispatch
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6R15ModeCost (word)
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R48DFS J6R49DFS J6R53Dispatch J1PPrinted
open J6R19Retained J6R23ScheduleWeight
noncomputable section

variable {f : ℤ[X]} {ell s q highPrec : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
local notation "Sp" => (printedParams (f:=f) (ell:=ell) s)
local notation "Wp" => J6R15ModeCost.Word q

def RawCentreChild (_sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)} (d : J6R12Blueprint.Ready Sp (sourceDelta s) c)
    (t : Center Sp c) (bank : Bank f) (q : ℕ) : Type :=
  Probe Sp c→List (J6R15ModeCost.Word q)→Fin 64→
    Meter (Block (bank (registerPrecision Sp c t) (register_positive d t)) ell)

def RawActiveChild (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)} (d : J6R12Blueprint.Ready Sp (sourceDelta s) c)
    (bank : Bank f) (q : ℕ) : Type :=
  ∀ t : Center Sp c,RawCentreChild sel d t bank q

def centreJetRaw (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (read : RawCentreChild sel d t bank q) :
    Meter (JetTape J.low.words ell J.window) :=
  fullCenterM J.low.hp J.low.sizePos hv
    (active_order_pos ((Sp).levelBits c.depth) c.edges ((Sp).levelWidth c.depth) t.val t.property)
    (fun z=>padCost (encodeProbe J.low.hp hv (J.masks z).result) (J.masks z).steps)
    (fun z=>probeExposed J.low J.tape.result hq hv (read z))
    (normalizerM J.low.hp J.low.sizePos hv
      (active_order_pos ((Sp).levelBits c.depth) c.edges ((Sp).levelWidth c.depth) t.val t.property)
      ((Sp).levelBits c.depth) t.val J.roster.rows)

def runCentreRaw (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (read : RawCentreChild sel d t bank q) : Meter (Block high ell) :=
  let w := centreJetRaw J hq hv read
  let out := sumM high.hp (J.centreTerm hv hf high B w.result) (List.range J.window)
  ⟨out.result,J.tape.steps+w.steps+out.steps+
    tapeFee J.low.words.length ell (registerPrecision Sp c t) J.window+4⟩

theorem centre_raw_uses_same_meter (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (read : RawCentreChild sel d t bank q)
    (typed : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (same : ∀ z β g,read z ((vectorKey sel d t J.tape.result β).map word) g=typed z β g) :
    runCentreRaw J hq hv hf high B read=J.runCentre hq hv hf high B typed := by
  have h : (fun z=>probeExposed J.low J.tape.result hq hv (read z))=
      (fun z=>runProbe J.low J.tape.result hq hv (typed z)) :=
    funext (fun z=>exposed_probe_is_same_meter J.low J.tape.result hq hv (read z) (typed z) (same z))
  have jet : centreJetRaw J hq hv read=J.centreJet hq hv typed := by
    unfold centreJetRaw CentreMachine.centreJet directCentreJet
    rw [h]
  unfold runCentreRaw CentreMachine.runCentre
  dsimp only
  rw [jet]

def evalRaw (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (read : RawActiveChild sel d bank q) : Meter (Block (bank c.prec hp) ell) :=
  let v := sumM (D.high hp).hp (fun t=>runCentreRaw (D.tape t) hq hv hf (D.high hp) D.extraPrecision (read t)) D.centres
  let rc := stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v.result
  checkedWord (zeroM (bank c.prec hp).hp) ⟨rc.result,v.steps+rc.steps+4⟩

theorem raw_active_is_same_meter (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (read : RawActiveChild sel d bank q) (typed : ActiveChild (sel:=sel) (d:=d) bank)
    (same : ∀ t z β g,read t z ((vectorKey sel d t (D.tape t).tape.result β).map word) g=typed t z β g) :
    evalRaw D hq hp hv hf read=D.eval hq hp hv hf typed := by
  have h : (fun t=>runCentreRaw (D.tape t) hq hv hf (D.high hp) D.extraPrecision (read t))=
      (fun t=>(D.tape t).runCentre hq hv hf (D.high hp) D.extraPrecision (typed t)) :=
    funext (fun t=>centre_raw_uses_same_meter (D.tape t) hq hv hf (D.high hp) D.extraPrecision
      (read t) (typed t) (same t))
  unfold evalRaw ActiveMachine.eval ActiveMachine.finish ActiveMachine.highRun
  rw [h]

#print axioms RawActiveChild
#print axioms centre_raw_uses_same_meter
#print axioms evalRaw
#print axioms raw_active_is_same_meter
end
end J6R55Dispatch
