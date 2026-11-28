import J6R55CachedLedgerCore

/-! A scope-fee necessity result. The exact same selected StoredSites
and the same actual build/lookup/rail words are compatible with
arbitrary padding in the unimplemented boot Meter. Width/semantic
correctness does not mathematically imply a running-time cap. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R51Online
open J6R55CachedLedger J6R53PeakAddon
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def padInitialDebit (M : OnlineMachine T key prec tw bw page q) (extra : ℕ) :
    OnlineMachine T key prec tw bw page q :=
  { M with initial := fun w =>
    let old := M.initial w
    ⟨old.result,old.steps+extra⟩ }

theorem boot_fee_padding_keeps_all_real_source_states
    (M : OnlineMachine T key prec tw bw page q) (extra : ℕ) :
    ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      sourceState (padInitialDebit M extra) p w=sourceState M p w := by
  intro x p
  induction p with
  | root => intro w; rfl
  | step p u ih =>
    intro w
    change ((M.demand (sourceState (padInitialDebit M extra) p u) w).result.advance).next =
      ((M.demand (sourceState M p u) w).result.advance).next
    rw [ih u]

theorem exact_boot_fee_padding_is_visible_in_the_actual_scope
    (M : OnlineMachine T key prec tw bw page q) (extra : ℕ)
    (retire : J→ℕ) (initial : L) (w : (Plan sel).Slot r) :
    cachedScopeOwn (padInitialDebit M extra) retire initial .root w=
      cachedScopeOwn M retire initial .root w+extra := by
  simp only [cachedScopeOwn,installedAddonDebit,borns,sourceBankAt,stackBank,
    sourceState,padInitialDebit]
  ac_rfl

theorem no_root_scope_cap_from_source_state_alone
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (w : (Plan sel).Slot r) (budget : ℕ) :
    let M' := padInitialDebit M (budget+1)
    (∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x),
      sourceState M' p u=sourceState M p u) ∧
      budget<cachedScopeOwn M' retire initial .root w := by
  refine ⟨boot_fee_padding_keeps_all_real_source_states M (budget+1),?_⟩
  change budget<cachedScopeOwn (padInitialDebit M (budget+1)) retire initial .root w
  rw [exact_boot_fee_padding_is_visible_in_the_actual_scope]
  omega

end
#print axioms boot_fee_padding_keeps_all_real_source_states
#print axioms exact_boot_fee_padding_is_visible_in_the_actual_scope
#print axioms no_root_scope_cap_from_source_state_alone
end J6R57ScopeFee
