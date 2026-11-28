import J6R54PeakInputRunner
import J6R53PeakAddonBoot

/-! Root-level attachment of the exact single-explicit-emission
recursion. The existing typed boot loader and its original input-supply
boundary remain unchanged. -/
namespace J6R54PeakInput
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R51Online J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 20500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def rootReadSingleEmission (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ)
    (bank : L) (a : (SP).cutoff<r.edges) :
    ActiveChild (sel:=sel) (d:=ready_reachable cfg sel (Path.root : Path sel r r).reached T.rootStable a) T.bank :=
  let here : Path sel r r := .root
  let d := ready_reachable cfg sel here.reached T.rootStable a
  fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    project (bootBankDemand (M.initial w) retire (runCachedAfterSingleEmission M retire r here w)
      (zeroM (T.bank (registerPrecision SP r t) (register_positive d t)).hp) bank)

theorem single_emission_first_reader_has_the_original_cached_meter
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (bank : L) (a : (SP).cutoff<r.edges) :
    rootReadSingleEmission M retire bank a=exteriorCachedRead M retire bank a := by
  funext t z β g
  let here : Path sel r r := .root
  let d := ready_reachable cfg sel here.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let F := T.bank (registerPrecision SP r t) (register_positive d t)
  let bad : Meter (Block F ell) := zeroM F.hp
  have unified : runCachedAfterSingleEmission M retire r here w=runCachedAfter M retire r here w := by
    funext next live
    exact all_depth_single_emission_preserves_cached_result_and_cost M retire r here w next live
  change project (bootBankDemand (M.initial w) retire (runCachedAfterSingleEmission M retire r here w)
      bad bank)=project (bootBankDemand (M.initial w) retire (runCachedAfter M retire r here w) bad bank)
  rw [unified]

def runCachedRootSingleEmission (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) :
    SM L (Block (T.frame (Path.root : Path sel r r).reached) ell) :=
  fun bank=>
    if stop : r.edges≤(SP).cutoff then
      let done := M.leafRoot stop bank
      ⟨(done.result,bank),done.steps⟩
    else
      let active := Nat.lt_of_not_ge stop
      let A := M.activeRoot active
      let here : Path sel r r := .root
      let done := A.result.eval M.modeWidth (reachable_positive T here.reached) T.vPositive hf
        (rootReadSingleEmission M retire bank active)
      ⟨(done.result,bank),A.steps+done.steps⟩

theorem the_entire_root_run_has_the_same_meter_with_single_deep_emission
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (bank : L) :
    runCachedRootSingleEmission M retire bank=runCachedRoot M retire bank := by
  by_cases stop : r.edges≤(SP).cutoff
  · rw [runCachedRootSingleEmission,dif_pos stop,runCachedRoot,dif_pos stop]
  · let active := Nat.lt_of_not_ge stop
    have h := single_emission_first_reader_has_the_original_cached_meter M retire bank active
    rw [runCachedRootSingleEmission,dif_neg stop,actual_root_active_uses_the_exterior_child_reader M retire bank active]
    dsimp only
    rw [h]

#print axioms single_emission_first_reader_has_the_original_cached_meter
#print axioms the_entire_root_run_has_the_same_meter_with_single_deep_emission
end
end J6R54PeakInput
