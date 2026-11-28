import J6R57ScopeFeeFootprinted
import J6R66ActiveExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14500000
set_option maxRecDepth 3800
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Inputs are individually observed acquisition operands and native
word/atlas dimensions. There is no premise bounding the entire scope
and no second publication of the already paid exterior. -/
namespace J6R67UnifiedRate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R55CachedLedger J6R57ScopeFee J6R64Active
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables J6R26StablePreparedRoot
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q pointerWidth : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)
local notation "Bnk" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

structure MeasuredScopeInputs (M : Machine) (initial : Bnk) where
  wordCaps : ScopeWordCaps
  fit : ScopeWordFits M initial wordCaps
  bootBudget : ℕ
  demandBudget : ℕ
  queryBudget : ℕ
  sourceWordBudget : ℕ
  atlasSize : ℕ
  boot : ∀ w : (P).Slot r, (M.initial w).steps≤bootBudget
  demand : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
    (u : (P).Slot x) (w : (P).Slot ((P).child x u)),
    (M.demand (sourceState M p u) w).steps≤demandBudget
  query : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
    (u : (P).Slot x) (w : (P).Slot ((P).child x u)),
    sidecarQueryBill (M.demand (sourceState M p u) w).result≤queryBudget
  sourceWords : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    measuredWordProducers (sourceState M p w).input≤sourceWordBudget
  footprint : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    AtlasFootprint (sourceState M p w).input atlasSize

def measuredPerScope {M : Machine} {B : Bnk} (F : MeasuredScopeInputs M B) (ptr : ℕ) :=
  derivedPerScope s C r.edges key prec tw bw page ptr B.headers.length B.records.length
    F.wordCaps (primitiveAndFootprintBudget F.bootBudget F.demandBudget F.queryBudget F.sourceWordBudget F.atlasSize)

theorem live_scope_has_derived_fee {M : Machine} {B : Bnk}
    (F : MeasuredScopeInputs M B) (tails : SavedDirectoryTails pointerWidth)
    (p : Path sel r c) (w : (P).Slot c) :
    cachedScopeOwn M (retireSavedDirectory tails) B p w≤measuredPerScope F pointerWidth :=
  actual_scope_cap_from_word_and_finite_resident_sizes M B tails F.wordCaps F.fit
    F.bootBudget F.demandBudget F.queryBudget F.sourceWordBudget F.atlasSize
    F.boot F.demand F.query F.sourceWords F.footprint ⟨c,p⟩ w

section PaidRoot
variable {V : Type} [Fintype V] {m n base native : ℕ} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {qr ro co de edgew tc tj pad : ℕ}
variable (X : StableExterior G ell qr ro co de edgew tc tj key prec tw bw)
local notation "PgB" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))

theorem already_paid_seed_supplies_both_live_certificates
    (prior : PgB) (paid : Meter (PgB×Bool))
    (source : paid=(X.seed pad).install prior)
    (ready : JobsReady prior [X.seed pad]) :
    let B := paid.result.1
    IsLive (X.seed pad) B ∧ OwnsHeader X.header.result B := by
  have recpt := (next_job_exact prior (X.seed pad) [] ready).1
  dsimp only
  rw [source,recpt]
  exact ⟨new_is_live (X.seed pad) prior,rfl⟩
end PaidRoot

#print axioms measuredPerScope
#print axioms live_scope_has_derived_fee
#print axioms already_paid_seed_supplies_both_live_certificates
end
end J6R67UnifiedRate

