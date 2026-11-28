import J6R116RetainedExteriorPeakActive
import J6R115RetainedPeakPathReach

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
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
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

local instance exteriorPathPeakEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

variable (D : KeptDrivers X M rank)
variable {x : KeptInvocation X M}

local notation "Start" => (firstInvocation X M initial boot E on w)

/-- From the actual first child of the original exterior evaluator
to a named descendant of its same execution plan. The exterior
packed output is used once, as that child's inherited input. -/
theorem actual_exterior_prefix_and_its_live_retained_path_share_one_roof
    (valid : ReadyOnStack (borns M) initial)
    (reach : NativeReach (retainedOccurrencePlan X M D) Start x)
    (ambient entryRoof frameRoof : ℕ)
    (held : ∀ {y : KeptInvocation X M},NativeReach (retainedOccurrencePlan X M D) Start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof)
    (entry : ∀ {y : KeptInvocation X M},NativeReach (retainedOccurrencePlan X M D) Start y→
      invocationEntryBits X M y (chartAndAmbient X M D (ambient+descriptorBits X))≤entryRoof) :
    let shared := chartAndAmbient X M D (ambient+descriptorBits X)
    let priorCut := exteriorBeforeFirstBits X M initial boot E on D ambient
    ∃ path : VisitedRetainedPath X M D Start x,
      max priorCut (visitedEntryPeak X M D shared path)≤entryRoof+pathLimit s C*frameRoof ∧
      ∀ prevActive : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges,
        activeRetainedBits X M D x prevActive shared≤entryRoof →
        max priorCut (max (visitedEntryPeak X M D shared path)
          (visitedCarry X M D path+activeRetainedBits X M D x prevActive shared))≤
          entryRoof+pathLimit s C*frameRoof := by
  let k := exteriorBeforeFirstBits X M initial boot E on D ambient
  have fit := entry (.reflexive Start)
  have first := first_scope_adds_one_install_and_reuses_the_extent_packed_words X M initial boot E on w D ambient
  change invocationEntryBits X M Start (chartAndAmbient X M D (ambient+descriptorBits X))≤entryRoof at fit
  rw [first] at fit
  have preRoof : k≤entryRoof := by
    change exteriorBeforeFirstBits X M initial boot E on D ambient≤_
    omega
  have preWide : k≤entryRoof+pathLimit s C*frameRoof := preRoof.trans (Nat.le_add_right _ _)
  have bank := (first_live_contains_the_original_words_and_published_stack X M initial boot E on w).1
  obtain ⟨path,_,peak,active⟩ := every_actual_retained_occurrence_has_its_named_peak_on_the_same_tree
    X M D initial bank valid reach (ambient+descriptorBits X) entryRoof frameRoof held entry
  exact ⟨path,max_le preWide peak,fun a h=>max_le preWide (active a h)⟩

#print axioms actual_exterior_prefix_and_its_live_retained_path_share_one_roof
end
end J6R116RetainedExteriorPeak

