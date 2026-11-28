import J6R111KeptOwnerFlowRunRoot
import J6R67UnifiedRateScope

/-! Metered incoming retained scope. The same carried first site and its
already-paid owner spool are used; no equality of whole runners is assumed. -/
namespace J6R116RetainedFirstTariff
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R68.RecursivePeak
open J6R111KeptOwnerFlow J6R53PeakAddon J6R55CachedLedger J6R57ScopeFee J6R67UnifiedRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section

section LocalDebit
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable (B : PageBank f ell key prec tw bw page)
variable (retire : PageJob f ell key prec tw bw page→ℕ)
variable {v : Ticket sel r}

/-- Local operations on a single paid stored receipt, independent of its
particular host graph or of the type of its continuation. -/
def incomingFirstDebit (first : Meter (StoredSite T v key prec tw bw page)) : ℕ :=
  let j := first.result.birth.job
  first.steps+(publishFee B j.entry j.offset j.built+
    ((installResidentBank first.result).steps+retire j+4))

private theorem regroupLocal (a b c d : ℕ) :
    a+(b+(c+d+4))=a+c+(b+d+4) := by omega

theorem compiler_initial_debit_matches_scope (w : (Plan sel).Slot r) :
    incomingFirstDebit B retire (M.initial w)=cachedScopeOwn M retire B (Path.root : Path sel r r) w := by
  let j := (M.initial w).result.birth.job
  exact regroupLocal (M.initial w).steps (publishFee B j.entry j.offset j.built)
    (installResidentBank (M.initial w).result).steps (retire j)
end LocalDebit

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (boot : FirstSource X M)
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))

/-- The actual carried first fee. The first receipt already includes
its owner roster's charge. No second exterior install is added. -/
def firstCarrierDebit : ℕ :=
  incomingFirstDebit initial retire
    (⟨(boot.make w).result.site,(boot.make w).steps⟩ : Meter (StoredSite T ((RootPath).ticket w) key prec tw bw (pageKeyWidth m+pad)))

/-- Full Meter identity, not just stored-header or value agreement, is
needed to substitute the verified R57 local fee. -/
theorem retained_first_debit_is_the_same_R57_local_charge :
    firstCarrierDebit X M initial boot w retire=cachedScopeOwn M retire initial RootPath w := by
  exact (congrArg (incomingFirstDebit initial retire) (boot.exact w)).trans
    (compiler_initial_debit_matches_scope M initial retire w)

theorem actual_carried_first_debit_within_R57
    {ptr : ℕ} (tails : SavedDirectoryTails ptr) (score : MeasuredScopeInputs M initial) :
    firstCarrierDebit X M initial boot w (retireSavedDirectory tails)≤measuredPerScope score ptr :=
  (retained_first_debit_is_the_same_R57_local_charge X M initial boot w
    (retireSavedDirectory tails)).le.trans (live_scope_has_derived_fee score tails RootPath w)

/-- Numerical regrouping of the actual `enterPaidFirst` receipt to
one local fee and the exact continuation fee. -/
theorem regroup_actual_first_receipt (a b c d e : ℕ) :
    a+(b+(c+e)+d+4)=a+(b+(c+d+4))+e := by omega

#print axioms compiler_initial_debit_matches_scope
#print axioms retained_first_debit_is_the_same_R57_local_charge
#print axioms actual_carried_first_debit_within_R57
#print axioms regroup_actual_first_receipt
end
end J6R116RetainedFirstTariff
