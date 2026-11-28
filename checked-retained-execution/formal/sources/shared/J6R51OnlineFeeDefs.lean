import J6R51OnlineRun
import J6R49CostRuntime

/-! Fees billed by the demand-driven runner, indexed by physical
occurrences rather than deduplicated calls. No legacy runner's
bill is substituted for actual local acquisition. -/
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
set_option maxHeartbeats 20000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
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
def onlineTotal (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (z : Sigma (Path sel r)) : ℕ := by
  rcases z with ⟨c,p⟩
  cases p with
  | root => exact (runRoot M retire initial).steps
  | step p u =>
    exact (runAfter M retire _ p u (sourceState M p u)
      (stackBank (borns M) initial (.step p u))).steps

def atSlotAcquisition (M : OnlineMachine T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (P).Slot c) : ℕ := by
  cases p with
  | root => exact (M.initial w).steps
  | step prev u => exact paidAcquisition (M.demand (sourceState M prev u) w)

def onlineScopeOwn (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (P).Slot c) : ℕ :=
  let j := (borns M p w).job
  atSlotAcquisition M p w +
    (publishFee (stackBank (borns M) initial p) j.entry j.offset j.built + retire j + 4)

def preparedActive (M : OnlineMachine T key prec tw bw page q)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (a : (S).cutoff<c.edges) :
    Meter (ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable a) T.bank q) := by
  cases p with
  | root => exact M.activeRoot a
  | step prev u => exact M.activeAfter prev u (sourceState M prev u) a

def readLeaf (M : OnlineMachine T key prec tw bw page q) (initial : L)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (stop : c.edges≤(S).cutoff) :
    Meter (Block (T.frame p.reached) ell) := by
  cases p with
  | root => exact M.leafRoot stop initial
  | step prev u =>
    exact M.leafAfter prev u (sourceState M prev u) stop (stackBank (borns M) initial (.step prev u))

def onlineOwn (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (initial : L) (z : Sigma (Path sel r)) : ℕ :=
  if stop : z.1.edges≤(S).cutoff then
    (readLeaf M initial z.2 stop).steps
  else
    let A := preparedActive M z.2 (Nat.lt_of_not_ge stop)
    letI : Fintype ((P).Slot z.1) := (P).finiteSlot z.1
    A.steps+streamActiveTariff A.result (reachable_positive T z.2.reached) T.vPositive+
      ∑ w : (P).Slot z.1,onlineScopeOwn M retire initial z.2 w

theorem online_leaf_total (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (stop : c.edges≤(S).cutoff) :
    onlineTotal M retire initial ⟨c,p⟩=(readLeaf M initial p stop).steps := by
  cases p with
  | root =>
    change (runRoot M retire initial).steps=(M.leafRoot stop initial).steps
    rw [runRoot,dif_pos stop]
  | step p u =>
    let bank := stackBank (borns M) initial (.step p u)
    let X := sourceState M p u
    change (runAfter M retire _ p u X bank).steps=(M.leafAfter p u X stop bank).steps
    rw [runAfter,dif_pos stop]

#print axioms onlineTotal
#print axioms atSlotAcquisition
#print axioms onlineScopeOwn
#print axioms preparedActive
#print axioms readLeaf
#print axioms onlineOwn
#print axioms online_leaf_total
end
end J6R51Online
