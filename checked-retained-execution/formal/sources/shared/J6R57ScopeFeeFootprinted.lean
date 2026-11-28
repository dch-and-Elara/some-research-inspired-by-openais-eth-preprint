import J6R57ScopeFeeLedger
import J6R57ScopeFeeAtlasGeometry

/-! The atlas line of the R56 scope phase is now obtained directly
from actual finite resident shape, rather than a bound on even the
explicit atlas tariff. Only genuine primitive metered acquisition
contracts are left for the caller to implement. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R50Peak J6R51Peak J6R51Online
open J6R55CachedLedger
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

def primitiveAndFootprintBudget (boot demand queries sourceWords U : ℕ) : PrimitiveCostCaps :=
  ⟨boot,demand,queries,sourceWords,atlasWordGeometryCeiling U⟩

theorem actual_scope_cap_from_word_and_finite_resident_sizes
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth)
    (W : ScopeWordCaps) (hW : ScopeWordFits M initial W)
    (boot demand queries words U : ℕ)
    (hBoot : ∀ w : (Plan sel).Slot r,(M.initial w).steps≤boot)
    (hDemand : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
      (u : (Plan sel).Slot x) (w : (Plan sel).Slot ((Plan sel).child x u)),
      (M.demand (sourceState M p u) w).steps≤demand)
    (hQueries : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
      (u : (Plan sel).Slot x) (w : (Plan sel).Slot ((Plan sel).child x u)),
      sidecarQueryBill (M.demand (sourceState M p u) w).result≤queries)
    (hWords : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      measuredWordProducers (sourceState M p w).input≤words)
    (hFoot : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
      AtlasFootprint (sourceState M p w).input U) :
    ∀ (z : Sigma (Path sel r)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn M (retireSavedDirectory tails) initial z.2 w≤
        derivedPerScope s C r.edges key prec tw bw page pointerWidth initial.headers.length
          initial.records.length W (primitiveAndFootprintBudget boot demand queries words U) := by
  let V := primitiveAndFootprintBudget boot demand queries words U
  have hV : PrimitiveCostFits M V := by
    refine ⟨hBoot,hDemand,hQueries,hWords,?_⟩
    intro x p w
    exact literal_atlas_tariff_from_finite_footprint (sourceState M p w).input U (hFoot p w)
  exact derived_scope_phase_field M initial tails W V hW hV

end
#print axioms primitiveAndFootprintBudget
#print axioms actual_scope_cap_from_word_and_finite_resident_sizes
end J6R57ScopeFee
