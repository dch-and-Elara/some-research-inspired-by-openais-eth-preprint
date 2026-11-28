import J6R116PhysicalRetainedChartImage
import J6R116RetainedExteriorPeakChart

/-! Named workspace on the same admitted and mounted row that the paid
count uses, with the native input size in the bound. -/
namespace J6R114PrescribedReceipts
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost
open J6R24LegalLayout J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R31RootResidentTables J6R32RootGeneratedRegistryInputs J6R34ChildPath
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R52FreshExterior J6R54PublicFamily J6R57PublicRequest J6R75OuterTime J6R14ZeroMode
open J6R109CanonicalProbeTable J6R110CanonicalMount J6R110CanonicalCoverage J6R110CanonicalAllPeak
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath J6R116RetainedExteriorPeak
open J6ActiveRun J6R9Recursive J6R10Reachable J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 25000000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable (image : RequestImage W I) (groups : PhysicalRetainedImagePlan image)
variable (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result =
  OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

local notation "Mounted" => (mountTheChartOnEveryChosenActualGroup image groups bytes)
local notation "Row" => (sourceRow (W:=W) image.compiled i j g)
local notation "Reply" => (admitTheEmittedRow image.compiled image.tables (Mounted).pad (Mounted).prior
    (Mounted).sync (Mounted).reserved i j g Row rfl).result
local notation "Held" => (Reply).payload
local notation "Prep" => (groups.acquire i j g Row rfl Reply)
local notation "Actual" => ((Mounted).acquire i j g Row rfl Reply).result
local notation "Ext" => (exteriorChild G ell (Held).site.centre (Held).site.sample (Held).site.group)
local notation "Spec" => (printedParams (f:=f) (ell:=ell) (Actual).size)
local notation "PlanOf" =>
  (retainedOccurrencePlan (Held).site (Actual).machine (Actual).drivers)

/-- At one real group address, combine the paid chart region with any
actually reached retained path of the installed chart. The live-frame and
entry bounds retain the hypotheses of the original named-buffer lemma. -/
theorem posted_row_workspace_uses_source_size
    (on : (Spec).cutoff<(Ext).edges) (w : (Plan (Actual).selector).Slot Ext)
    {x : KeptInvocation (Held).site (Actual).machine}
    (reach : NativeReach PlanOf (firstOfOnePaidChart Held Prep bytes on w) x)
    (ambient entryRoof frameRoof built : ℕ)
    (cut : CanonicalBootCut (Prep).result.prepared bytes built)
    (held : ∀ {y : KeptInvocation (Held).site (Actual).machine},
      NativeReach PlanOf (firstOfOnePaidChart Held Prep bytes on w) y →
      (Spec).cutoff<y.call.edges→suspendedParentBits (Held).site (Actual).machine y≤frameRoof)
    (entry : ∀ {y : KeptInvocation (Held).site (Actual).machine},
      NativeReach PlanOf (firstOfOnePaidChart Held Prep bytes on w) y →
      invocationEntryBits (Held).site (Actual).machine y
        (chartAndAmbient (Held).site (Actual).machine (Actual).drivers
          (ambient+descriptorBits (Held).site))≤entryRoof) :
    let A := Actual
    let shared := chartAndAmbient (Held).site A.machine A.drivers (ambient+descriptorBits (Held).site)
    let startup := chartStartupAmbient Held ambient
    let pre := exteriorBeforeFirstBits (Held).site A.machine (Held).receipt.1 A.first A.exterior on A.drivers ambient
    A.drivers.masks=(mountFullChart (Prep).result.prepared bytes).result ∧
    ((Mounted).acquire i j g Row rfl Reply).steps=(Prep).steps+(mountFullChart (Prep).result.prepared bytes).steps+4 ∧
    ∃ path : VisitedRetainedPath (Held).site A.machine A.drivers (firstOfOnePaidChart Held Prep bytes on w) x,
      max (startup+built) (max pre (visitedEntryPeak (Held).site A.machine A.drivers shared path))≤
        max (startup+264*(physicalSize m native)^5) (entryRoof+pathLimit (physicalSize m native) 2*frameRoof) := by
  have sizeAndConstant := posted_and_mounted_payload_has_source_scale image groups bytes i j g
  have exactPeak := actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
    Held Prep bytes on w reach ambient entryRoof frameRoof built cut held entry
  obtain ⟨chart, fee, path, peak⟩ := exactPeak
  refine ⟨chart, fee, path, ?_⟩
  calc
    _ ≤ max (chartStartupAmbient Held ambient + 264 * (Actual).size^5)
        (entryRoof + pathLimit (Actual).size (Actual).constant * frameRoof) := peak
    _ = _ := congrArg₂ max
      (congrArg (fun s => chartStartupAmbient Held ambient + 264 * s^5) sizeAndConstant.1)
      (congrArg₂ (fun s c => entryRoof + pathLimit s c * frameRoof) sizeAndConstant.1 sizeAndConstant.2.1)

#print axioms posted_row_workspace_uses_source_size
end
end J6R114PrescribedReceipts
