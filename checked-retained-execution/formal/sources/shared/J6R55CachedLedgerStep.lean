import J6R55CachedLedgerCore
import J6R51AbsoluteLedger
import J6R49CostRuntime

/-! Expand each actual cache-aware read as its own fee plus the true
recursive response, and sum the actual occurrences with repetitions. -/
namespace J6R55CachedLedger
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3900
set_option maxHeartbeats 26000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)
local notation "Plan₀" => (@Plan f ell s sel)

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_cached_fee_step (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (z : Sigma (Path sel r)) :
    cachedTotal M retire initial z ≤ cachedOwn M retire initial z+
      ((childList (nativeScopedPlan sel r) z).map (cachedTotal M retire initial)).sum := by
  rcases z with ⟨c,p⟩
  by_cases stop : c.edges≤(SP).cutoff
  · rw [cached_leaf_total M retire initial p stop,cachedOwn,dif_pos stop]
    exact Nat.le_add_right _ _
  · let a := Nat.lt_of_not_ge stop
    let A := preparedActive M p a
    let hp := reachable_positive T p.reached
    let read := cachedReadAt M retire initial p a
    let own := cachedScopeOwn M retire initial p
    let child := fun w : (Plan₀).Slot c=>cachedTotal M retire initial ⟨(Plan₀).child c w,.step p w⟩
    letI : Fintype ((Plan₀).Slot c) := (Plan₀).finiteSlot c
    have hs := (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
    obtain ⟨hu,_,huM⟩ := printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size a hs
    have math := actual_stream_active_word_meter A.result M.modeWidth hp T.vPositive hf hu huM read
    have calls : streamActiveChildBill A.result read = ∑ w : (Plan₀).Slot c,(own w+child w) := by
      apply stream_active_child_bill_matches_slots A.result T.vPositive read (fun w=>own w+child w)
      intro t zz β g
      exact cached_read_steps_sum M retire initial p a legal t zz β g
    have sumCalls := (childList_bill_as_sum (nativeScopedPlan sel r) ⟨c,p⟩
      (cachedTotal M retire initial)).symm
    change (∑ w : (Plan₀).Slot c,child w)=_ at sumCalls
    rw [calls,Finset.sum_add_distrib,sumCalls] at math
    rw [cached_active_total_eq M retire initial p a,cachedOwn,dif_neg stop]
    change cacheMountFee M p+A.steps+(A.result.eval M.modeWidth hp T.vPositive hf read).steps ≤
      cacheMountFee M p+A.steps+streamActiveTariff A.result hp T.vPositive+(∑ w : (Plan₀).Slot c,own w)+_
    exact (Nat.add_le_add_left math _).trans (le_of_eq (by ac_rfl))

theorem actual_cached_occurrence_ledger (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (rootFit : r.depth≤pathLimit s C) :
    (runCachedRoot M retire initial).steps ≤
      ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (cachedOwn M retire initial) j :=
  paid_run_from_absolute_depth cfg sel r T.rootStable rootFit
    (cachedTotal M retire initial) (cachedOwn M retire initial)
    (actual_cached_fee_step M retire initial legal)

#print axioms actual_cached_fee_step
#print axioms actual_cached_occurrence_ledger
end
end J6R55CachedLedger
