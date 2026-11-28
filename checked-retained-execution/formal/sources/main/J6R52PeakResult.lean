
import J6R52PeakBudget
import J6R52PeakReached
import J6R51OnlineCorrect

/-! The value and selected path bound concern one particular online
runner, not an identification of its fee or memory with a prepared
runner. Explicit width and legal live-bank receipts still apply. -/
namespace J6R52Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R50Peak J6R51Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 18000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_online_value_and_actual_selected_peak (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial)
    (qFit : q≤uniformWidth s C) (pageBound high fixed addr seed : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed) :
    let out := runRoot M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
      (sourceBlueprint sel r hf).program.run r ∧ out.result.2=initial ∧
    ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x),
      OnlineChargePath M retire initial p ∧ ∃ b,OnlineTrace M retire initial p b ∧
        residentAtlasBits (stackBank (borns M) initial p)+b+directoryBits (stackBank (borns M) initial p)≤
          actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed := by
  obtain ⟨v,restored⟩ := full_online_selected_source M initial retire legal leaves
  exact ⟨v,restored,fun p=>⟨every_legal_online_path_has_actual_paid_chronology M retire initial legal p,
    actual_online_path_has_joint_selected_bound M retire initial
      qFit pageBound high fixed addr seed pageFit hi sizes boot p⟩⟩

#print axioms same_online_value_and_actual_selected_peak
end J6R52Peak
