
import J6R51OnlineVisitDefs

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
set_option maxHeartbeats 6200000
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

def activeAt (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
    Meter (ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable a) T.bank q)
  | _,.root,a => M.activeRoot a
  | _,.step prev u,a => M.activeAfter prev u (sourceState M prev u) a

#print axioms activeAt

def readAt (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
    ActiveChild (sel:=sel) (d:=ready_reachable cfg sel p.reached T.rootStable a) T.bank
  | _,.root,a => readRoot M retire a initial
  | _,.step prev u,a => readAfter M retire prev u (sourceState M prev u) a
      (stackBank (borns M) initial (.step prev u))

#print axioms readAt

def runAt (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) →
    Meter (Block (T.frame p.reached) ell × L)
  | _,.root => runRoot M retire initial
  | _,.step prev u => runAfter M retire _ prev u (sourceState M prev u)
      (stackBank (borns M) initial (.step prev u))

#print axioms runAt

def acquisitionAt (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (w : (P).Slot x) → ℕ
  | _,.root,w => (M.initial w).steps
  | _,.step prev u,w => paidAcquisition (M.demand (sourceState M prev u) w)

#print axioms acquisitionAt
end
end J6R52Peak
