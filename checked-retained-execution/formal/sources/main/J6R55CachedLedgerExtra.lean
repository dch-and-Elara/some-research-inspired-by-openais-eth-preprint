import J6R55CachedLedgerCore

/-! The cache ledger does not re-charge a descendant's sidecar install.
In its comparison with the older online tariff only a real root index
install and a once-per-active-descendant frame mount are additional. -/
namespace J6R55CachedLedger
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3850
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Plan₀" => (@Plan f ell s sel)

def additionalRootIndexFee (M : OnlineMachine T key prec tw bw page q) :
    {c : Call (PhysicalHost f ell)} → (p : Path sel r c) → (Plan₀).Slot c → ℕ
  | _, .root, w => (sourceBankAt M .root w).steps
  | _, .step _ _, _ => 0

theorem cached_scope_only_adds_the_original_root_index
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan₀).Slot c) :
    cachedScopeOwn M retire initial p w =
      onlineScopeOwn M retire initial p w+additionalRootIndexFee M p w := by
  cases p with
  | root =>
    simp only [cachedScopeOwn,onlineScopeOwn,installedAddonDebit,atSlotAcquisition,
      additionalRootIndexFee]
    ac_rfl
  | step p u =>
    simp only [cachedScopeOwn,onlineScopeOwn,installedAddonDebit,atSlotAcquisition,
      additionalRootIndexFee,Nat.add_zero]

def additionalCachedOwn (M : OnlineMachine T key prec tw bw page q)
    (z : Sigma (Path sel r)) : ℕ :=
  if z.1.edges≤(SP).cutoff then 0 else
    letI : Fintype ((Plan₀).Slot z.1) := (Plan₀).finiteSlot z.1
    cacheMountFee M z.2+∑ w : (Plan₀).Slot z.1,additionalRootIndexFee M z.2 w

theorem cached_occurrence_fee_has_no_duplicate_descendant_install
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (z : Sigma (Path sel r)) :
    cachedOwn M retire initial z=onlineOwn M retire initial z+additionalCachedOwn M z := by
  rcases z with ⟨c,p⟩
  by_cases stop : c.edges≤(SP).cutoff
  · simp only [cachedOwn,onlineOwn,additionalCachedOwn,dif_pos stop,if_pos stop,Nat.add_zero]
  · letI : Fintype ((Plan₀).Slot c) := (Plan₀).finiteSlot c
    have fees : (∑ w : (Plan₀).Slot c,cachedScopeOwn M retire initial p w)=
        (∑ w : (Plan₀).Slot c,onlineScopeOwn M retire initial p w)+
        (∑ w : (Plan₀).Slot c,additionalRootIndexFee M p w) := by
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun w _=>cached_scope_only_adds_the_original_root_index M retire initial p w)
    simp only [cachedOwn,onlineOwn,additionalCachedOwn,dif_neg stop,if_neg stop]
    rw [fees]
    ac_rfl

#print axioms cached_scope_only_adds_the_original_root_index
#print axioms cached_occurrence_fee_has_no_duplicate_descendant_install
end
end J6R55CachedLedger
