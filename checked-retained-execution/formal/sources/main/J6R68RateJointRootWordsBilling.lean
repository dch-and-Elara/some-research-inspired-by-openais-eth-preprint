import J6R68RateJointRootWordsBillingBoot
import J6R67UnifiedRateScope

/-! The measured scope contract does not acquire root fees indirectly
through a full assumed scope cap. All non-first obligations remain
separate; attach root setup and root native issuance as their own lines. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion J6R53PeakAddon J6R55CachedLedger
open J6ActiveRun J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R52CacheWhole J6R48DFS J6R64Active
open J6R57ScopeFee J6R67UnifiedRate

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4400
set_option maxHeartbeats 8200000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "Here" => (Path.root : Path sel r r)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
local notation "Site" => (fun w : (P).Slot r=>StoredSite T ((Here).ticket w) key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page rate)

/-- Precisely the supplied fields unchanged by verified first-entry
charging. In particular no root initial fee or root word fee is here. -/
structure RemainingScopeInputs (M : Machine) (B : L) where
  wordCaps : ScopeWordCaps
  fit : ScopeWordFits M B wordCaps
  demandBudget : ℕ
  queryBudget : ℕ
  descendantWords : ℕ
  atlasSize : ℕ
  demand : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c)
    (w : (P).Slot ((P).child c u)),(M.demand (sourceState M p u) w).steps≤demandBudget
  query : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c)
    (w : (P).Slot ((P).child c u)),sidecarQueryBill (M.demand (sourceState M p u) w).result≤queryBudget
  words : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (P).Slot c)
    (w : (P).Slot ((P).child c u)),measuredWordProducers (sourceState M (.step p u) w).input≤descendantWords
  footprint : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (P).Slot c),
    AtlasFootprint (sourceState M p w).input atlasSize

def scopeWithActualFirst {M : Machine} {B : L} (Q : RemainingScopeInputs M B)
    (boot native : ℕ) (onBoot : ∀ w : (P).Slot r,(M.initial w).steps≤boot)
    (onWords : ∀ w : (P).Slot r,measuredWordProducers (sourceState M Here w).input≤native) :
    MeasuredScopeInputs M B where
  wordCaps := Q.wordCaps
  fit := Q.fit
  bootBudget := boot
  demandBudget := Q.demandBudget
  queryBudget := Q.queryBudget
  sourceWordBudget := max native Q.descendantWords
  atlasSize := Q.atlasSize
  boot := onBoot
  demand := Q.demand
  query := Q.query
  footprint := Q.footprint
  sourceWords := by
    intro _ p w
    cases p with
    | root => exact (onWords w).trans (le_max_left _ _)
    | step p u => exact (Q.words p u w).trans (le_max_right _ _)

theorem counted_r66_first_boot_uses_scope_bound {M : Machine} (w : (P).Slot r)
    {Out : Type} {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (child : (next : Site w)→WithIncoming next Out) (bad : Meter Out)
    (B : L) (legal : ReadyOnStack (borns M) B) (F : MeasuredScopeInputs M B) :
    let first := M.initial w
    let j := first.result.birth.job
    let mounted := installResidentBank first.result
    let after := child first.result mounted.result (j.install B).result.1
      (successful_publish_has_exact_head j B (real_first_install_ok B j (legal Here w)))
    let spent := bootWithHeader first (retireSavedDirectory tails) child bad B
    spent.result=(after.result.1,B) ∧ spent.steps≤measuredPerScope F pointerWidth+after.steps := by
  obtain ⟨v,paid⟩ := r66_first_boot_exact_own_debit M w (retireSavedDirectory tails) child bad B legal
  exact ⟨v,paid.le.trans (Nat.add_le_add_right (live_scope_has_derived_fee F tails Here w) _)⟩

#print axioms scopeWithActualFirst
#print axioms counted_r66_first_boot_uses_scope_bound
end
end J6R68RateJoint.RootWords

