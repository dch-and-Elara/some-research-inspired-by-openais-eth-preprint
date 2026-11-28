import J6R49DFSDirectCentre
import J6R24MeteredRecursionCentre

/-! Runtime centre uses only an ordered tape of variables, their
weights and precision. Legacy complete mode lists appear only in
the separate proof-side priorCentre map. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 J6R22Active J6R23ScheduleWeight
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R9Recursive J6R24MeteredRecursion J1PPrinted

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 2300

structure CentreMachine {f : ℤ[X]} {ell s : ℕ}
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)}
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c)
    (bank : Bank f) (q : ℕ) where
  roster : J6R23ScheduleWeight.Roster ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
    c.edges ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth) t.val
  masks : Probe (printedParams (f:=f) (ell:=ell) s) c →
    Meter {m : List Bool // m.length =
      (bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t)
        (register_positive d t)).words.length}
  literal : ∀ z,(masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ d.fit z)
  tape : Meter (J6R16ModeCost.SiteTape sel d t q)

variable {f : ℤ[X]} {ell s q highPrec : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}

abbrev CentreMachine.low (_J : CentreMachine sel d t bank q) :=
  bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (register_positive d t)

abbrev CentreMachine.window (_J : CentreMachine sel d t bank q) :=
  order c.edges ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth) t.val

noncomputable def CentreMachine.centreTerm (J : CentreMachine sel d t bank q)
    (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (jet : JetTape J.low.words ell J.window) (j : ℕ) : Meter (Block high ell) :=
  termM J.low.hp J.low.sizePos high.hp high.sizePos hv
    ((J.low.natDegree hf).trans (high.natDegree hf).symm)
    jet ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth) B j t.val J.roster.rows

noncomputable def CentreMachine.centreJet (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    Meter (JetTape J.low.words ell J.window) :=
  directCentreJet J.low J.tape.result hq hv
    (active_order_pos ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
      c.edges ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows child

noncomputable def CentreMachine.runCentre (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank) : Meter (Block high ell) :=
  let w := J.centreJet hq hv child
  let out := sumM high.hp (J.centreTerm hv hf high B w.result) (List.range J.window)
  ⟨out.result,J.tape.steps+w.steps+out.steps+
    tapeFee J.low.words.length ell (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) J.window+4⟩

noncomputable def CentreMachine.priorCentre (J : CentreMachine sel d t bank q)
    (modes : List (NativeMenu (N sel) c t)) (nd : modes.Nodup) (complete : ∀ β,β∈modes) :
    CentreDesc sel d t bank :=
  ⟨J.roster,J.masks,J.literal,modes,nd,complete⟩

#print axioms CentreMachine
#print axioms CentreMachine.centreTerm
#print axioms CentreMachine.centreJet
#print axioms CentreMachine.runCentre
end J6R49DFS
