import J6R49DFSCentre

/-! Exact active replacement without a catalogue field. The legacy
complete mode lists occur only in the proof-side prior method. -/
namespace J6R49DFS
open scoped Polynomial Classical
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R23ScheduleWeight J6R19Retained
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J6R24MeteredRecursion J1PPrinted HermiteLoss

set_option autoImplicit false
set_option maxRecDepth 2600
set_option maxHeartbeats 8500000

structure ActiveMachine {f : ℤ[X]} {ell s : ℕ}
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)}
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (bank : Bank f) (q : ℕ) where
  extraPrecision : ℕ
  enough : commonLoss ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
    c.edges ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth) ≤ extraPrecision
  centres : List (Center (printedParams (f:=f) (ell:=ell) s) c)
  centreUnique : centres.Nodup
  centreComplete : ∀ t,t∈centres
  tape : ∀ t,CentreMachine sel d t bank q

variable {f : ℤ[X]} {ell s q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}

abbrev ActiveMachine.high (D : ActiveMachine sel d bank q) (hp : 0<c.prec) :
    Frame f (c.prec+D.extraPrecision) :=
  bank (c.prec+D.extraPrecision) (Nat.lt_of_lt_of_le hp (Nat.le_add_right c.prec D.extraPrecision))

noncomputable def ActiveMachine.highRun (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) : Meter (Block (D.high hp) ell) :=
  sumM (D.high hp).hp (fun t=>(D.tape t).runCentre hq hv hf (D.high hp) D.extraPrecision (child t)) D.centres

noncomputable def ActiveMachine.finish (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    Meter (Option (Block (bank c.prec hp) ell)) :=
  let v := D.highRun hq hp hv hf child
  let rc := stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v.result
  ⟨rc.result,v.steps+rc.steps+4⟩

noncomputable def ActiveMachine.eval (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) : Meter (Block (bank c.prec hp) ell) :=
  checkedWord (zeroM (bank c.prec hp).hp) (D.finish hq hp hv hf child)

/-- Ghost comparison; never used by ActiveMachine.eval. -/
noncomputable def ActiveMachine.prior (D : ActiveMachine sel d bank q) :
    ActiveDesc sel d bank where
  extraPrecision := D.extraPrecision
  enough := D.enough
  centres := D.centres
  centreUnique := D.centreUnique
  centreComplete := D.centreComplete
  tape t :=
    letI : Fintype (NativeMenu (N sel) c t) := nativeMenuFinite (N sel) c t
    (D.tape t).priorCentre Finset.univ.toList (Finset.nodup_toList _) (fun b=>by simp)

theorem active_high_stream_value (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    (D.highRun hq hp hv hf child).result=(D.prior.highRun hp hv hf child).result := by
  apply sum_raw_congr
  intro t _
  letI : Fintype (NativeMenu (N sel) c t) := nativeMenuFinite (N sel) c t
  exact centre_stream_value (D.tape t) hq hv hf (D.high hp) D.extraPrecision (child t)
    Finset.univ.toList (Finset.nodup_toList _) (fun b=>by simp)

theorem active_finish_stream_value (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    (D.finish hq hp hv hf child).result=(D.prior.finish hp hv hf child).result := by
  change (stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm)
    (D.highRun hq hp hv hf child).result).result=
    (stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm)
    (D.prior.highRun hp hv hf child).result).result
  rw [active_high_stream_value D hq hp hv hf child]

theorem active_stream_value (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    (D.eval hq hp hv hf child).result=(D.prior.eval hp hv hf child).result := by
  have e := active_finish_stream_value D hq hp hv hf child
  unfold ActiveMachine.eval ActiveDesc.eval checkedWord
  rw [e]
  cases (D.prior.finish hp hv hf child).result <;> rfl

#print axioms ActiveMachine.eval
#print axioms active_high_stream_value
#print axioms active_finish_stream_value
#print axioms active_stream_value
end J6R49DFS
