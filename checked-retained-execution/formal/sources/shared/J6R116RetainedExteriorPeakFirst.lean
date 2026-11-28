import J6R116RetainedExteriorPeakDescriptor
import J6R111KeptOwnerFlowRunRoot
import J6R114RetainedPeakEntry

/-! The first captured entry is the argument passed by the literal
exterior callback. This observer neither reissues the exterior
row nor prepares a different first child. -/
namespace J6R116RetainedExteriorPeak
open scoped Polynomial Classical
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
open J6R111KeptOwnerFlow J6R114RetainedPeak
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
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
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))

local notation "RootCall" => (exteriorChild G ell X.centre X.sample X.group)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))
local notation "Started" => (boot.make w)
local notation "FirstSite" => (boot.make w).result.site

local instance exteriorPeakEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

def exteriorPackedAtFirstScope := selectedLayoutAndLabels (E.setup on)

def labelsAtFirstScope :=
  useAlreadyEmittedLabels X RootPath w FirstSite (Started).result.owners (E.setup on)
    (exteriorPackedAtFirstScope X M boot E on).result rfl
    (Started).result.injective (E.order on w) (E.exactLabels on)

def firstCapture : CapturedEntry X RootPath w FirstSite :=
  ⟨(installResidentBank FirstSite).result,afterOne initial (FirstSite).birth.job,rfl,
    (Started).result.owners,labelsAtFirstScope X M boot E on w⟩

def firstInvocation : KeptInvocation X M :=
  ⟨RootCall,RootPath,w,FirstSite,congrArg Meter.result (boot.exact w),
    firstCapture X M initial boot E on w⟩

theorem first_live_contains_the_original_words_and_published_stack :
    let x := firstInvocation X M initial boot E on w
    x.entry.bank=stackBank (borns M) initial (Path.step RootPath w) ∧
    x.entry.resident=(installResidentBank FirstSite).result ∧
    x.entry.owners.raw=(Started).result.owners.raw ∧
    packedKeptBits x.entry.labelled.raw=packedKeptBits (exteriorPackedAtFirstScope X M boot E on).result := by
  refine ⟨?_,rfl,rfl,rfl⟩
  have site : FirstSite=sourceState M RootPath w := congrArg Meter.result (boot.exact w)
  change afterOne initial (FirstSite).birth.job=_
  rw [site]
  rfl

variable (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

def actualExteriorFirstCallback
    (bad : Meter (Block (T.frame (Path.step RootPath w).reached) ell)) :=
  enterPaidFirst X initial retire w Started
    (fun arg=>runRetained X M D retire ⟨RootCall,RootPath,w,FirstSite,
      congrArg Meter.result (boot.exact w),arg⟩)
    (labelsAtFirstScope X M boot E on w) bad

theorem the_actual_first_scope_resumes_this_same_observed_invocation
    (valid : ReadyOnStack (borns M) initial)
    (bad : Meter (Block (T.frame (Path.step RootPath w).reached) ell)) :
    let first := firstInvocation X M initial boot E on w
    let next := (Started).result.site
    let j := next.birth.job
    let out := runRetained X M D retire first
    actualExteriorFirstCallback X M initial boot E on w D retire bad=
      ⟨(out.result.1,initial),(Started).steps+
        (publishFee initial j.entry j.offset j.built+
          ((installResidentBank next).steps+out.steps)+retire j+4)⟩ := by
  have agreement : FirstSite=sourceState M RootPath w := congrArg Meter.result (boot.exact w)
  have legal : JobsReady initial [(FirstSite).birth.job] := by
    rw [agreement]
    exact valid RootPath w
  exact the_paid_first_carrier_enters_one_live_resident_and_restores_parent
    X initial retire w Started _ (labelsAtFirstScope X M boot E on w) bad legal

#print axioms firstInvocation
#print axioms first_live_contains_the_original_words_and_published_stack
#print axioms the_actual_first_scope_resumes_this_same_observed_invocation
end
end J6R116RetainedExteriorPeak

