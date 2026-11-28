import J6R51OnlineFeeDefs
import J6R51OnlineVisitEq

/-! An emitted centre/probe/mode/group consumes the exact paid
continuation used by this online run. -/
namespace J6R51Online
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3400
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
variable (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)

def onlineRead (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    ActiveChild (sel:=sel) (d:=d) T.bank := by
  cases p with
  | root => exact readRoot M retire a initial
  | step prev u =>
    let B := stackBank (borns M) initial (.step prev u)
    exact readAfter M retire prev u (sourceState M prev u) a B

theorem online_active_total_eq (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (a : (S).cutoff<c.edges) :
    let A := preparedActive M p a
    onlineTotal M retire initial ⟨c,p⟩=A.steps+
      (A.result.eval M.modeWidth (reachable_positive T p.reached) T.vPositive hf
        (onlineRead M retire initial p a)).steps := by
  cases p with
  | root =>
    exact congrArg Meter.steps (run_root_active_eq M retire a initial)
  | step p u =>
    let B := stackBank (borns M) initial (.step p u)
    let X := sourceState M p u
    exact congrArg Meter.steps (run_after_active_eq M retire p u X a B)

#print axioms onlineRead
#print axioms online_active_total_eq
end
end J6R51Online
