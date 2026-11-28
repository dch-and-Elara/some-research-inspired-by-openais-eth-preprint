import J6R55CachedLedgerStep
import J6R54PeakInputRootRunner
import J6R52CacheWholeRoot

/-! The very R54 one-emission runner returns the mathematically exact
word, restores its bank, and has the actual measured occurrence bill. -/
namespace J6R55CachedLedger
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput

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
local notation "Pg" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_single_emission_cached_ledger (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (rootFit : r.depth≤pathLimit s C) :
    (runCachedRootSingleEmission M retire initial).steps ≤
      ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (cachedOwn M retire initial) j := by
  rw [the_entire_root_run_has_the_same_meter_with_single_deep_emission]
  exact actual_cached_occurrence_ledger M retire initial legal rootFit

theorem same_single_emission_value_and_actual_occurrence_bill (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    (legal : ReadyOnStack (borns M) initial) (leaves : LeafAgreement M initial)
    (rootFit : r.depth≤pathLimit s C) :
    let out := runCachedRootSingleEmission M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
        (sourceBlueprint sel r hf).program.run r ∧ out.result.2=initial ∧
      out.steps ≤ ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (cachedOwn M retire initial) j := by
  dsimp only
  rw [the_entire_root_run_has_the_same_meter_with_single_deep_emission]
  obtain ⟨value,restored⟩ := fully_cached_selected_source M initial retire legal leaves
  exact ⟨value,restored,actual_cached_occurrence_ledger M retire initial legal rootFit⟩

#print axioms same_single_emission_cached_ledger
#print axioms same_single_emission_value_and_actual_occurrence_bill
end
end J6R55CachedLedger
