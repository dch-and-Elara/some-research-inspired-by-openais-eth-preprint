import J6R49DFSScopedProbe
import J6R49CostProbeCensus
import J6R49CostScopePublish

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 20000000
set_option maxRecDepth 2800

/-! The same executable R49 scoped-probe adapter, now with a per-child
fee equality. Its descendants are R48 scoped runs. This deliberately
does not relabel them as the prospective whole-depth R49 streamer. -/
namespace J6R49Cost
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem actual_scoped_probe_child_bill (R : PagedResident T key prec tw bw page) (retire : J → ℕ)
    (initial : L) (legal : ReadyOnStack R.births initial) (p : Path sel r c)
    (a : (S).cutoff<c.edges) (t : Center S c) (z : Probe S c)
    (β : NativeMenu (J6R12Blueprint.N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    (scopedProbeChild R retire p a (stackBank R.births initial p) t z β g).steps =
      scopedPublishCharge R.births initial p w retire+
      (nativeScoped R retire ((Plan sel).child c w) (.step p w)
        (stackBank R.births initial (.step p w))).steps := by
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let χ := nativeScoped R retire ((Plan sel).child c w) (.step p w)
  exact actual_ready_scope_edge_steps R.births initial p w legal retire χ (zeroM F.hp)

theorem real_scoped_probe_arithmetic_and_subtree_bill (R : PagedResident T key prec tw bw page) (retire : J → ℕ)
    (initial : L) (legal : ReadyOnStack R.births initial) (p : Path sel r c)
    (a : (S).cutoff<c.edges) (t : Center S c) (z : Probe S c) (hq : 0<q)
    (I : SiteTape sel (ready_reachable cfg sel p.reached T.rootStable a) t q) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let F := T.bank (registerPrecision S c t) (register_positive d t)
    let formalChild := scopedProbeChild R retire p a (stackBank R.births initial p) t z
    letI : Fintype (NativeMenu (J6R12Blueprint.N sel) c t) := nativeMenuFinite (J6R12Blueprint.N sel) c t
    (runProbe F I hq T.vPositive formalChild).steps ≤
      (∑ β : NativeMenu (J6R12Blueprint.N sel) c t, ∑ g : Fin 64,
        let w := addressed (sel:=sel) d t z β g
        scopedPublishCharge R.births initial p w retire+
          (nativeScoped R retire ((Plan sel).child c w) (.step p w)
            (stackBank R.births initial (.step p w))).steps)+
      ((16*q+14+4*(I.words.length+1)*(q+1))+
        uvWidth F.words.length ell (registerPrecision S c t)+
        Nat.card (NativeMenu (J6R12Blueprint.N sel) c t)*perModeArithmetic F.words.length ell (registerPrecision S c t) F.hp+
        (Nat.card (NativeMenu (J6R12Blueprint.N sel) c t)+1)*J6R15ModeCost.delayCap q I.words.length) := by
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let read := scopedProbeChild R retire p a (stackBank R.births initial p) t z
  have bill := actual_streamed_probe_indexed_bill F I hq T.vPositive read
  dsimp only
  refine bill.trans (Nat.add_le_add_right ?_ _)
  unfold actualProbeChildBill
  exact Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun g _ =>
    (actual_scoped_probe_child_bill R retire initial legal p a t z β g).le))

#print axioms actual_scoped_probe_child_bill
#print axioms real_scoped_probe_arithmetic_and_subtree_bill
end J6R49Cost

