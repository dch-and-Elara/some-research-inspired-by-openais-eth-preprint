
import J6R52PeakReaderDefs
import J6R51OnlineVisitEq

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

theorem actual_online_active_phase (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let D := activeAt M p a
    let out := D.result.eval M.modeWidth (reachable_positive T p.reached) T.vPositive hf
      (readAt M retire initial p a)
    runAt M retire initial p=⟨(out.result,stackBank (borns M) initial p),D.steps+out.steps⟩ := by
  cases p with
  | root => exact run_root_active_eq M retire a initial
  | step prev u => exact run_after_active_eq M retire prev u (sourceState M prev u) a _

theorem actual_online_restores_path_bank (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) :
    (runAt M retire initial p).result.2=stackBank (borns M) initial p := by
  cases p with
  | root => exact root_run_restores_bank M retire initial
  | step prev u => exact inherited_run_restores_bank M retire _ prev u (sourceState M prev u) _

#print axioms actual_online_active_phase
#print axioms actual_online_restores_path_bank
end
end J6R52Peak
