import J6R52OnlineFeeReadSlot
import J6R51AbsoluteLedger

/-! The actual online interpreter's operation meter is bounded by its
occurrence ledger, with a relative range for any legal absolute root.
The entries explicitly include every acquisition and publication. -/
namespace J6R51Online
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3450
set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
variable (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem online_fee_step (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (legal : ReadyOnStack (borns M) initial) (z : Sigma (Path sel r)) :
    onlineTotal M retire initial z ≤ onlineOwn M retire initial z+
      ((childList (nativeScopedPlan sel r) z).map (onlineTotal M retire initial)).sum := by
  rcases z with ⟨c,p⟩
  by_cases stop : c.edges≤(S).cutoff
  · rw [online_leaf_total M retire initial p stop,onlineOwn,dif_pos stop]
    exact Nat.le_add_right _ _
  · let a := Nat.lt_of_not_ge stop
    let A := preparedActive M p a
    let hp := reachable_positive T p.reached
    let read := onlineRead M retire initial p a
    let own := onlineScopeOwn M retire initial p
    let child := fun w : (P).Slot c=>onlineTotal M retire initial ⟨(P).child c w,.step p w⟩
    letI : Fintype ((P).Slot c) := (P).finiteSlot c
    have hs := (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
    obtain ⟨hu,_,huM⟩ := printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size a hs
    have math := actual_stream_active_word_meter A.result M.modeWidth hp T.vPositive hf hu huM read
    have calls : streamActiveChildBill A.result read = ∑ w : (P).Slot c,(own w+child w) := by
      apply stream_active_child_bill_matches_slots A.result T.vPositive read (fun w=>own w+child w)
      intro t zz β g
      exact online_read_steps_sum M retire initial p a legal t zz β g
    have sumCalls := (childList_bill_as_sum (nativeScopedPlan sel r) ⟨c,p⟩
      (onlineTotal M retire initial)).symm
    change (∑ w : (P).Slot c,child w)=_ at sumCalls
    rw [calls,Finset.sum_add_distrib,sumCalls] at math
    rw [online_active_total_eq M retire initial p a,onlineOwn,dif_neg stop]
    change A.steps+(A.result.eval M.modeWidth hp T.vPositive hf read).steps ≤
      A.steps+streamActiveTariff A.result hp T.vPositive+(∑ w : (P).Slot c,own w)+_
    exact (Nat.add_le_add_left math _).trans (le_of_eq (by ac_rfl))

theorem same_online_run_paid_ledger (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (legal : ReadyOnStack (borns M) initial)
    (rootFit : r.depth≤pathLimit s C) :
    (runRoot M retire initial).steps ≤
      ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (onlineOwn M retire initial) j :=
  paid_run_from_absolute_depth cfg sel r T.rootStable rootFit
    (onlineTotal M retire initial) (onlineOwn M retire initial)
    (online_fee_step M retire initial legal)

#print axioms online_fee_step
#print axioms same_online_run_paid_ledger
end J6R51Online
