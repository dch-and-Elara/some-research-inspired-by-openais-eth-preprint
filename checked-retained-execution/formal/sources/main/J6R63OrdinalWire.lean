import J6R63OrdinalScope
import J6R58OrdinalSpaceNativeLoad
import J6R58OrdinalSpaceEventUnique

/-! Actual R58 checked ordinal bytes enter the original R54 cached
single-emission scope, not a hypothetical replacement oracle.
Changing only the dispatch search changes the bill by exactly that
phase; publication, installed resident bank and continuation are the
same. The caller's real archive/pulse evidence supplies the carrier. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R52CacheWhole J6R54PeakInput J6R52Dispatch J6R58OrdinalSpace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3300
set_option maxHeartbeats 11000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}
variable {U : ExplicitSelectedWords X.site u q} {R : Replayed X.site u q U}
variable {raw : List (Word (q+1))} {Out : Type}

theorem current_ordinal_enters_the_real_single_emission_scope
    (W : RankedEventFields R raw) (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (prior : Meter (Option (EventBytes (q+1) W.tc W.tz W.tm))) (good : CheckedEvent R prior)
    (cache : CachedParentFrames X.site) (retire : J → ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) →
      ResidentBank next → SM L Out)
    (fallback : Meter Out) (bank : L) :
    let one := loadUsingOrdinal W shell directory
    let old := acceptLocalLoad R shell directory prior good
    let latest := openBankDemandSingleEmission one cache retire child fallback bank
    let reference := openBankDemandSingleEmission old cache retire child fallback bank
    latest.result=reference.result ∧
      latest.steps+prior.steps=reference.steps+(rankedDispatch W).steps := by
  let newEvent := rankedDispatch W
  let newGood := (real_ranked_dispatch_is_checked_and_prices_only_replay W).1
  let acquired := acceptLocalLoad R shell directory newEvent newGood
  let legacy := acceptLocalLoad R shell directory prior good
  have shared : acquired.result=legacy.result :=
    genuine_acceptance_depends_on_event_not_its_search_fee R shell directory newEvent prior newGood good
  change (openBankDemandSingleEmission acquired cache retire child fallback bank).result=
      (openBankDemandSingleEmission legacy cache retire child fallback bank).result ∧
    (openBankDemandSingleEmission acquired cache retire child fallback bank).steps+prior.steps=
      (openBankDemandSingleEmission legacy cache retire child fallback bank).steps+newEvent.steps
  constructor
  · exact singular_scope_keeps_same_result_with_current_load acquired legacy cache retire
      child child fallback bank shared (fun _ _ _=>rfl)
  · simp only [single_local_emission_is_exactly_the_original_scoped_meter]
    unfold openBankDemand
    dsimp only
    rw [shared]
    have newCost : acquired.steps=newEvent.steps+6 := rfl
    have oldCost : legacy.steps=prior.steps+6 := rfl
    rw [newCost,oldCost]
    omega

#print axioms current_ordinal_enters_the_real_single_emission_scope
end
end J6R63Ordinal
