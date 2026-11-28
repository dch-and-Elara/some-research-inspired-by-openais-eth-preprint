
import J6R52PeakReaderDefs
import J6R51OnlineVisitCharge

/-! The actual online runner at each reached occurrence. The
sourceState is the already selected demanded state; it is not an
additional prebuilt input to the runner. Observational definitions
read the same child callbacks as the actual root and descendant. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R49DFS J6R50SourceProducer J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem actual_online_read_transaction (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (legal : ReadyOnStack (borns M) initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let B := stackBank (borns M) initial p
    let j := (borns M p w).job
    let out := runAt M retire initial (Path.step p w)
    readAt M retire initial p a t z β g =
      ⟨out.result.1,acquisitionAt M p w+(publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ ∧
    out.result.2=afterOne B j := by
  cases p with
  | root =>
    let p : Path sel r r := .root
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let F := T.bank (registerPrecision S r t) (register_positive d t)
    let bad : Meter (Block F ell) := zeroM F.hp
    simp only [readAt, acquisitionAt, runAt, stackBank, borns, sourceState]
    refine ⟨?_,inherited_run_restores_bank M retire r p w (M.initial w).result _⟩
    change project (bootDemand (M.initial w) retire (runAfter M retire r p w) bad initial)=_
    rw [boot_demand_exact (M.initial w) retire _ bad initial (legal p w)]
    rfl
  | step prev u =>
    let p := Path.step prev u
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let B := stackBank (borns M) initial p
    have h := actual_after_read_charge M retire prev u (sourceState M prev u) a B
      t z β g (legal p w)
    simpa only [p,B,readAt,acquisitionAt,runAt,stackBank,borns,sourceState] using h

#print axioms actual_online_read_transaction
end
end J6R52Peak
