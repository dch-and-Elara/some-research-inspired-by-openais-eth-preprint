import J6R116RunReadyRetainedPayload
import J6R117RetainedExteriorClockFinish
import J6R117RetainedExteriorClockGeometry
import J6R68AbsolutePrescribedSeed

/-! Same-bank contraction pricing of the already returned ready payload.
No runner is redefined, and no bound on its entire fee is assumed. -/
namespace J6R118ReadyRootClock
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R28GeneratedRootFrame J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak J6R16ModeCost
open J6R116RetainedExteriorPeak J6R49Cost J6R57ActiveFee J6R116RetainedPrefix J6R67UnifiedRate
open J6R58ActivePrep J6R48BitCost J6R50Peak

open J6R117RetainedExteriorClock J6R57PublicRequest J6R54PublicFamily J6R52FreshExterior
open J6R57ScopeFee J6R68AbsolutePrescribed J6R56PrintedExponent J6R51
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7200000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj kp prec tw bw : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {Cpt : Compiled G ell q ro co de prec kp bw} {pad : ℕ}
variable (a : ResidentAdmissionCarry (W:=W) Cpt pad)
variable (A : ReadyRetainedPayload a)

local notation "RootCall" => (exteriorChild G ell a.site.centre a.site.sample a.site.group)
local notation "Bank" => (a.receipt.1)
local notation "SP" => (printedParams (f:=f) (ell:=ell) A.size)

local instance readyRootClockEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

/-- The actual prescribed exterior, including the printed non-native last
probe, has the original absolute seed at the source's recorded scale. -/
theorem loaded_original_scale_has_its_prescribed_seed
    (sizeExact : A.size=physicalSize m native) (constantExact : A.constant=2)
    (baseFit : base≤2*physicalSize m native) :
    AbsoluteSeed A.size A.constant RootCall := by
  rw [sizeExact,constantExact]
  exact original_prescribed_exterior_seed G ell a.site.centre a.site.sample a.site.group baseFit

variable {ptr : ℕ} (tails : SavedDirectoryTails ptr)

/-- Only local measured and geometric fields of the supplied actual
payload. Descendant conditions are confined to the actual first calls
and their actual reached occurrences, and the stop bound is on the
original terminal, not a replacement branch. -/
structure ReadyContractionInputs where
  retirement : A.retire=retireSavedDirectory tails
  seed : AbsoluteSeed A.size A.constant RootCall
  scope : MeasuredScopeInputs A.machine Bank
  wordBudget : ℕ
  layoutCap : ℕ
  wordFit : ExteriorIncomingFits tc tj prec edgew A.rank wordBudget
  scale : ActiveWidthScale (ell:=ell) (s:=A.size) (C:=A.constant) (q:=A.rate) (r:=RootCall) wordBudget
  centres : PrintedCentreScale A.size A.constant wordBudget
  absoluteHigh : absolutePrecision A.size (RootCall).edges (RootCall).prec+
      (A.constant*A.size)*(24*2^(Nat.clog 2 A.size)+4*(Nat.clog 2 A.size+1))≤wordBudget
  layoutPaid : ∀ on : (SP).cutoff<(RootCall).edges, (A.exterior.setup on).run.steps≤layoutCap
  fixed : ℕ
  address : ℕ
  localAt : ∀ (on : (SP).cutoff<(RootCall).edges)
      (w : (Plan A.selector).Slot RootCall) (j : ℕ) (y : KeptInvocation a.site A.machine),
      y∈occurrences (retainedOccurrencePlan a.site A.machine A.drivers)
        (firstInvocation a.site A.machine Bank A.first A.exterior on w) j →
      y.entry.bank=stackBank (borns A.machine) Bank (.step y.path y.slot) →
      retainedOwnTariff a.site A.machine A.drivers A.retire y Bank ≤
        fixed+address*Nat.card ((Plan A.selector).Slot y.call)
  stopCap : ℕ
  stopped : ∀ stop : (RootCall).edges≤(SP).cutoff,(A.machine.leafRoot stop Bank).steps≤stopCap

variable {tails}
variable (C : ReadyContractionInputs a A tails)

/-- R68's printed native slot bound on this very loaded exterior. -/
def prescribedAddressRoof : ℕ :=
  2^(branchBits (Nat.clog 2 A.size)+
    depthExponent A.size A.constant (Nat.clog 2 A.size) (siteConstant A.constant) (RootCall).depth)

def actualExteriorFixedPrice (K layoutCap : ℕ) : ℕ :=
  sweptSetupPx K (layoutCap+4)+fixedArithmeticPx K (preparedCentrePx K) (mountedMaskPx K)

def readySuffixCharge : ℕ :=
  (pathLimit A.size A.constant-(RootCall).depth)*(C.fixed+C.address)*
    2^(fullPrefixConstant A.constant*J9PrintedSchedule.leafThreshold A.size (Nat.clog 2 A.size))

def readyActiveContractionRoof : ℕ :=
  let N := prescribedAddressRoof a A
  actualExteriorFixedPrice C.wordBudget C.layoutCap + physicalAddressUnit C.wordBudget*N+
    N*(measuredPerScope C.scope ptr+readySuffixCharge a A C)

def readyRootContractionRoof : ℕ := max C.stopCap (readyActiveContractionRoof a A C)

variable (owns : OwnsHeader a.site.header.result a.receipt.1)
local notation "Paid" => (runRetainedExterior a.site A.machine a.receipt.1 owns A.first A.drivers A.exterior A.retire)

/-- Price exactly the contraction consumed by `physicalRowsOnThatImage`.
The small branch is the original `leafRoot` Meter. The active branch
uses the R117 actual geometry, first slots and original tapered suffix. -/
theorem ready_root_contracts_on_its_paid_bank_with_derived_roof :
    (Paid).steps≤readyRootContractionRoof a A C := by
  by_cases stop : (RootCall).edges≤(SP).cutoff
  · have paid : (Paid).steps=(A.machine.leafRoot stop Bank).steps := by
      rw [C.retirement]
      exact congrArg Meter.steps (actual_prescribed_exterior_stop_runs_its_original_terminal
        a.site A.machine Bank A.first A.exterior owns A.drivers tails stop)
    rw [paid]
    exact (C.stopped stop).trans (le_max_left _ _)
  · let on := Nat.lt_of_not_ge stop
    let N := prescribedAddressRoof a A
    let M := Nat.card ((Plan A.selector).Slot RootCall)
    let b := actualExteriorFixedPrice C.wordBudget C.layoutCap
    let unit := physicalAddressUnit C.wordBudget
    let inner := measuredPerScope C.scope ptr+readySuffixCharge a A C
    have geom := exterior_active_prefix_uses_captured_geometry a.site A.machine Bank A.first
      A.exterior on owns A.drivers C.wordBudget C.layoutCap C.wordFit C.scale C.centres
      (C.layoutPaid on) C.absoluteHigh
    have clock := actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
      a.site A.machine Bank A.first A.exterior on owns A.drivers tails C.scope
      (fun {_} p w=>A.valid p w) C.seed b unit C.fixed C.address geom.1 geom.2
      (by
        intro w j y seen live
        rw [←C.retirement]
        exact C.localAt on w j y seen live)
    have addresses : M≤N := absolute_seed_live_addresses_bound A.bounds A.selector C.seed
    have actual : (Paid).steps≤b+unit*M+M*inner := by
      rw [C.retirement]
      exact clock
    have upper : (Paid).steps≤readyActiveContractionRoof a A C :=
      actual.trans (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ addresses) _)
        (Nat.mul_le_mul_right _ addresses))
    exact upper.trans (le_max_right _ _)

theorem ready_root_contracts_on_its_paid_bank_with_alpha
    (α : ℕ) (fits : readyRootContractionRoof a A C≤α) : (Paid).steps≤α :=
  (ready_root_contracts_on_its_paid_bank_with_derived_roof a A C owns).trans fits

#print axioms loaded_original_scale_has_its_prescribed_seed
#print axioms ready_root_contracts_on_its_paid_bank_with_derived_roof
#print axioms ready_root_contracts_on_its_paid_bank_with_alpha
end
end J6R118ReadyRootClock
