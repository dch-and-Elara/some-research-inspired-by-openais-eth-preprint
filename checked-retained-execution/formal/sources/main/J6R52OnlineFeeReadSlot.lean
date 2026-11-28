import J6R52OnlineFeeReadDefs
import J6R51OnlineVisitEq
import J6R51OnlineVisitCharge

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
set_option maxHeartbeats 7500000
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

theorem online_read_steps_sum (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (a : (S).cutoff<c.edges) (legal : ReadyOnStack (borns M) initial)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    (onlineRead M retire initial p a t z β g).steps=
      onlineScopeOwn M retire initial p w +
        onlineTotal M retire initial ⟨(P).child c w,.step p w⟩ := by
  cases p with
  | root =>
    let d := ready_reachable cfg sel (Path.root : Path sel r r).reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let K := M.initial w
    let j := K.result.birth.job
    let next := runAfter M retire r .root w K.result (afterOne initial j)
    let F := T.bank (registerPrecision S r t) (register_positive d t)
    let bad : Meter (Block F ell) := zeroM F.hp
    have h := boot_demand_exact K retire (runAfter M retire r .root w) bad initial (legal .root w)
    change (project (bootDemand K retire (runAfter M retire r .root w) bad initial)).steps=
      K.steps+(publishFee initial j.entry j.offset j.built+retire j+4)+next.steps
    calc
      _ = K.steps+(publishFee initial j.entry j.offset j.built+next.steps+retire j+4) :=
        congrArg (fun a=> (project a).steps) h
      _ = _ := by ac_rfl
  | step prev u =>
    let p := Path.step prev u
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let bank := stackBank (borns M) initial p
    let X := sourceState M prev u
    let K := M.demand X w
    let nxt := K.result.advance.next
    let j := nxt.birth.job
    let next := runAfter M retire _ p w nxt (afterOne bank j)
    have h := (actual_after_read_charge M retire prev u X a bank t z β g (legal p w)).1
    change (readAfter M retire prev u X a bank t z β g).steps=
      paidAcquisition K+(publishFee bank j.entry j.offset j.built+retire j+4)+next.steps
    calc
      _ = paidAcquisition K + (publishFee bank j.entry j.offset j.built+next.steps+retire j+4) :=
        congrArg Meter.steps h
      _ = _ := by ac_rfl

#print axioms online_read_steps_sum
end
end J6R51Online
