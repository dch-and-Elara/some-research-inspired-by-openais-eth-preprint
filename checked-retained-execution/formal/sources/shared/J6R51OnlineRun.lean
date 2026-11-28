import J6R51OnlineCore

/-! Execute the actual selected native stream with one stored incoming
occurrence. The child continuations get the very object made by their
publication; they do not look up a job in a tree. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3400
set_option maxHeartbeats 11500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (Plan sel)

def runAfter
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) :
    SM L (Block (T.frame (Path.step p u).reached) ell) :=
  let current := (P).child c u
  let path := Path.step p u
  if stop : current.edges≤(S).cutoff then
    fun B=>
      let w := M.leafAfter p u X stop B
      ⟨(w.result,B),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeAfter p u X active
    fun B=>
      let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
        (fun t z β g=>
          let w := addressed (sel:=sel) d t z β g
          let K := M.demand X w
          project (openDemand K retire (fun next=>runAfter M retire current path w next)
            (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B))
      ⟨(out.result,B),A.steps+out.steps⟩
termination_by ((Plan sel).child c u).edges
decreasing_by exact (Plan sel).smaller ((Plan sel).child c u) w

theorem inherited_run_restores_bank
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (c : Call (PhysicalHost f ell)) (p : Path sel r c) (u : (P).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page) (B : L) :
    (runAfter M retire c p u X B).result.2=B := by
  by_cases stop : ((P).child c u).edges≤(S).cutoff
  · rw [runAfter,dif_pos stop]
  · rw [runAfter,dif_neg stop]

/-- A first edge has no predecessor occurrence, so its genuine root
loader is used instead of the descendant loader. It too is invoked
only at the actual current slot. -/
def bootDemand {w : (P).Slot r} {R : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retireJob : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page→SM L R)
    (fallback : Meter R) (B : L) : Meter (R×L) :=
  let start := boot.result
  let out := withScope retireJob start.birth.job (child start) fallback B
  ⟨out.result,boot.steps+out.steps⟩

theorem boot_demand_exact {w : (P).Slot r} {R : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retireJob : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page→SM L R)
    (fallback : Meter R) (B : L) (ready : JobsReady B [boot.result.birth.job]) :
    let spec := boot.result
    let job := spec.birth.job
    let out := child spec (afterOne B job)
    bootDemand boot retireJob child fallback B=
      ⟨(out.result.1,B),boot.steps+(publishFee B job.entry job.offset job.built+out.steps+retireJob job+4)⟩ := by
  unfold bootDemand
  dsimp only
  rw [paid_scope_exact retireJob _ _ _ B ready]

def runRoot
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) : SM L (Block (T.frame (Path.root : Path sel r r).reached) ell) :=
  if stop : r.edges≤(S).cutoff then
    fun B=>
      let w := M.leafRoot stop B
      ⟨(w.result,B),w.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let path : Path sel r r := .root
    let d := ready_reachable cfg sel path.reached T.rootStable active
    let A := M.activeRoot active
    fun B=>
      let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
        (fun t z β g=>
          let w := addressed (sel:=sel) d t z β g
          project (bootDemand (M.initial w) retire (runAfter M retire r path w)
            (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B))
      ⟨(out.result,B),A.steps+out.steps⟩

theorem root_run_restores_bank
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (B : L) :
    (runRoot M retire B).result.2=B := by
  by_cases stop : r.edges≤(S).cutoff
  · rw [runRoot,dif_pos stop]
  · rw [runRoot,dif_neg stop]

#print axioms runAfter
#print axioms inherited_run_restores_bank
#print axioms boot_demand_exact
#print axioms runRoot
#print axioms root_run_restores_bank
end
end J6R51Online