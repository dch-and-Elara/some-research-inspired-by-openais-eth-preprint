import J6R117RetainedExteriorClockSeed
import J6R117RetainedExteriorClockFold

/-! Same-meter exterior group time, including one genuine charge at each
first slot and every actual retained descendant. The native absolute seed
is valid also at the original last prescribed (non-prefix) sample. -/
namespace J6R117RetainedExteriorClock
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
open J6R116RetainedExteriorPeak J6R116RetainedFirstTariff J6R49Cost J6R57ActiveFee J6R55CachedLedger
open J6R57ScopeFee J6R67UnifiedRate J6R68AbsolutePrescribed J6R51 J6R56PrintedExponent

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (boot : FirstSource X M) (E : ExteriorLabels X M boot rank)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges)

local notation "RootCall" => (exteriorChild G ell X.centre X.sample X.group)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))

local instance exteriorClockFinishEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

variable (head : OwnsHeader X.header.result initial)
variable (D : KeptDrivers X M rank)



variable {ptr : ℕ} (tails : SavedDirectoryTails ptr)
variable (score : MeasuredScopeInputs M initial)

local notation "Policy" => (retireSavedDirectory tails)
local notation "ScheduleAt" => (exteriorSchedule X M initial boot E on head D)
local notation "Paid" => (runRetainedExterior X M initial head boot D E (retireSavedDirectory tails))
local notation "L" => (Nat.clog 2 s)
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "PC" => (fullPrefixConstant C)

/-- A group has one exterior setup and one first-local bill at each
native address. The displayed suffix factor is the actual remaining
absolute depth, not a fresh restored depth-zero budget. -/
theorem actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
    (valid : ReadyOnStack (borns M) initial)
    (seed : AbsoluteSeed s C RootCall)
    (extFixed extUnit fixed address : ℕ)
    (rootPrefixCap : (ScheduleAt).steps+fixedActive (ScheduleAt).result.proofView
      (reachable_positive T (RootPath).reached) T.vPositive≤extFixed)
    (unit : ∀ t∈(ScheduleAt).result.proofView.centres,
      unitMode ((ScheduleAt).result.proofView.tape t).low ((ScheduleAt).result.proofView.tape t).tape.result≤64*extUnit)
    (localCap : ∀ (w : (Plan sel).Slot RootCall) (j : ℕ) (y : KeptInvocation X M),
      y ∈ occurrences (retainedOccurrencePlan X M D) (firstInvocation X M initial boot E on w) j →
      y.entry.bank=stackBank (borns M) initial (.step y.path y.slot) →
      retainedOwnTariff X M D Policy y initial ≤ fixed+address*Nat.card ((Plan sel).Slot y.call)) :
    (Paid).steps≤extFixed+extUnit*Nat.card ((Plan sel).Slot RootCall)+
      Nat.card ((Plan sel).Slot RootCall)*(measuredPerScope score ptr+
        (pathLimit s C-(RootCall).depth)* (fixed+address)*2^(PC*H)) := by
  let cp := (pathLimit s C-(RootCall).depth)*(fixed+address)*2^(PC*H)
  let P := Plan sel
  let charge := firstSlotBill X M initial boot E on D Policy
  letI : Fintype (P.Slot RootCall) := P.finiteSlot RootCall
  have fold := actual_exterior_active_clock_sums_the_issued_first_slots X M initial boot E on head D
    Policy valid extFixed extUnit rootPrefixCap unit
  have first (w : P.Slot RootCall) : charge w≤measuredPerScope score ptr+cp := by
    let x := firstInvocation X M initial boot E on w
    have bank : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot) :=
      (first_live_contains_the_original_words_and_published_stack X M initial boot E on w).1
    have suffix := actual_retained_subtree_from_prescribed_absolute_seed X M D Policy x initial bank valid
      seed fixed address (localCap w)
    have lev : x.call.depth=(RootCall).depth+1 := rfl
    have remaining : pathLimit s C-x.call.depth+1≤pathLimit s C-(RootCall).depth := by
      have f := retained_at_actual_root_has_bounded_absolute_depth X M seed.depth x
      omega
    have child : (runRetained X M D Policy x).steps≤cp :=
      suffix.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ remaining))
    have localFee : firstCarrierDebit X M initial boot w Policy≤measuredPerScope score ptr :=
      (retained_first_debit_is_the_same_R57_local_charge X M initial boot w Policy).le.trans
        (live_scope_has_derived_fee score tails RootPath w)
    exact Nat.add_le_add localFee child
  have summed : (∑ w : P.Slot RootCall,charge w)≤Nat.card (P.Slot RootCall)*(measuredPerScope score ptr+cp) := by
    calc
      _≤∑ _ : P.Slot RootCall, (measuredPerScope score ptr+cp) := Finset.sum_le_sum (fun w _=>first w)
      _=_ := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
        rfl
  exact fold.trans (Nat.add_le_add_left summed _)

/-- If the true exterior is already below the leaf cutoff, no first
scope is entered. Its bill and output are the same `leafRoot` Meter. -/
theorem actual_prescribed_exterior_stop_runs_its_original_terminal
    (stop : (RootCall).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    runRetainedExterior X M initial head boot D E Policy=
      ⟨((M.leafRoot stop initial).result,initial),(M.leafRoot stop initial).steps⟩ := by
  rw [runRetainedExterior,dif_pos stop]

#print axioms actual_prescribed_exterior_clock_with_real_first_and_retained_subtrees
#print axioms actual_prescribed_exterior_stop_runs_its_original_terminal
end
end J6R117RetainedExteriorClock
