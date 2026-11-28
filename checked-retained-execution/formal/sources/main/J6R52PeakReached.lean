import J6R52PeakMode
import J6R52PeakTransaction

/-! Successful physical occurrence routing for the real online evaluator,
with no additional run or future descriptor tape as input. 
The writes and the recursive callback are exactly those in its original
Meter. The inductive chain is only proof data. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R49DFS J6R50SourceProducer J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 17000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def SelectedOnlineCharge (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (w : (P).Slot c) : Prop :=
    let B := stackBank (borns M) initial p
    let j := (borns M p w).job
    let out := runAt M retire initial (Path.step p w)
    readAt M retire initial p w.property w.val.1 w.val.2.1 w.val.2.2.1 w.val.2.2.2=
      ⟨out.result.1,acquisitionAt M p w+(publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ ∧
    out.result.2=afterOne B j

theorem the_exact_slot_uses_the_same_online_call (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (legal : ReadyOnStack (borns M) initial)
    (p : Path sel r c) (w : (P).Slot c) :
    SelectedOnlineCharge M retire initial p w := by
  have transaction := actual_online_read_transaction M retire initial legal p w.property
    w.val.1 w.val.2.1 w.val.2.2.1 w.val.2.2.2
  have same := slot_is_literal_online_address (T:=T) p w
  dsimp only at same transaction
  simpa only [SelectedOnlineCharge,←same] using transaction

inductive OnlineChargePath (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → Prop where
  | root : OnlineChargePath M retire initial (.root : Path sel r r)
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x}
      (previous : OnlineChargePath M retire initial p) (w : (P).Slot x)
      (here : SelectedOnlineCharge M retire initial p w) :
      OnlineChargePath M retire initial (.step p w)

theorem every_legal_online_path_has_actual_paid_chronology
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial) (p : Path sel r c) :
    OnlineChargePath M retire initial p := by
  induction p with
  | root => exact .root
  | step p w ih =>
    exact .enter ih w (the_exact_slot_uses_the_same_online_call M retire initial legal p w)

#print axioms the_exact_slot_uses_the_same_online_call
#print axioms every_legal_online_path_has_actual_paid_chronology
end J6R52Peak
