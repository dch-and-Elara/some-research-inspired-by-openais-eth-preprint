import J6R116RetainedExteriorPeakPath
import J6R116ReadyRetainedChart
import J6R110CanonicalAllPeakBoot

/-! The newly generated chart and the retained path belong to the
same prepared continuation of this actual returned site and bank.
Consequently their named regional extrema combine by maximum. -/
namespace J6R116RetainedExteriorPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R34RootAtlas J6R28GeneratedRootFrame
open J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R26DescriptorTree
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50SourceProducer J6R51Online J6R52FreshExterior J6R54PublicFamily J6R57PublicRequest
open J6R64Active J6R66Active J6R66.BootPeak J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R10Reachable J6R16ModeCost
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
open J6R110CanonicalMount J6R110CanonicalCoverage J6R109CanonicalProbeTable J6R110CanonicalAllPeak

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23000000
set_option maxRecDepth 5000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj kp prec tw bw : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {Cpt : Compiled G ell q ro co de prec kp bw} {pad : ℕ}
variable (admitted : ResidentAdmissionCarry (W:=W) Cpt pad)
variable (preparation : Meter (ReadyRetainedPayload admitted))
variable (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result=
  OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))

local notation "ReadyData" => ((prepareWithPaidOriginalOrder admitted preparation bytes).result)
local notation "Ext" => (exteriorChild G ell admitted.site.centre admitted.site.sample admitted.site.group)
local notation "Spec" => (printedParams (f:=f) (ell:=ell) (ReadyData).size)

/-- Proof-side name for the invocation that the installed chart's
actual exterior first scope consumes. The admitted site stays the same. -/
abbrev firstOfOnePaidChart (on : (Spec).cutoff<(Ext).edges) (w : (Plan (ReadyData).selector).Slot Ext) :=
  firstInvocation admitted.site (ReadyData).machine admitted.receipt.1
    (ReadyData).first (ReadyData).exterior on w

/-- Ambient during the one actual chart-generation/installation
phase. Any other prior live fields, including any independently
already held input, are included in the supplied ambient. -/
def chartStartupAmbient (ambient : ℕ) : ℕ :=
  ambient+descriptorBits admitted.site+mountedSelectedBits admitted.receipt.1

/-- This peak combines the actual mount with the actual first/retained
path in its literal returned branch. It prices only the stated
named fields, not the preprocessing or arithmetic scratch. -/
theorem actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
    (on : (Spec).cutoff<(Ext).edges) (w : (Plan (ReadyData).selector).Slot Ext)
    {x : KeptInvocation admitted.site (ReadyData).machine}
    (reach : NativeReach (retainedOccurrencePlan admitted.site (ReadyData).machine (ReadyData).drivers)
      (firstOfOnePaidChart admitted preparation bytes on w) x)
    (ambient entryRoof frameRoof built : ℕ)
    (cut : CanonicalBootCut preparation.result.prepared bytes built)
    (held : ∀ {y : KeptInvocation admitted.site (ReadyData).machine},
      NativeReach (retainedOccurrencePlan admitted.site (ReadyData).machine (ReadyData).drivers)
        (firstOfOnePaidChart admitted preparation bytes on w) y →
      (Spec).cutoff<y.call.edges→suspendedParentBits admitted.site (ReadyData).machine y≤frameRoof)
    (entry : ∀ {y : KeptInvocation admitted.site (ReadyData).machine},
      NativeReach (retainedOccurrencePlan admitted.site (ReadyData).machine (ReadyData).drivers)
        (firstOfOnePaidChart admitted preparation bytes on w) y →
      invocationEntryBits admitted.site (ReadyData).machine y
        (chartAndAmbient admitted.site (ReadyData).machine (ReadyData).drivers (ambient+descriptorBits admitted.site))≤entryRoof) :
    let A := ReadyData
    let shared := chartAndAmbient admitted.site A.machine A.drivers (ambient+descriptorBits admitted.site)
    let startup := chartStartupAmbient admitted ambient
    let pre := exteriorBeforeFirstBits admitted.site A.machine admitted.receipt.1 A.first A.exterior on A.drivers ambient
    A.drivers.masks=(mountFullChart preparation.result.prepared bytes).result ∧
    (prepareWithPaidOriginalOrder admitted preparation bytes).steps=
      preparation.steps+(mountFullChart preparation.result.prepared bytes).steps+4 ∧
    ∃ path : VisitedRetainedPath admitted.site A.machine A.drivers
        (firstOfOnePaidChart admitted preparation bytes on w) x,
      max (startup+built) (max pre (visitedEntryPeak admitted.site A.machine A.drivers shared path))≤
        max (startup+264*A.size^5) (entryRoof+pathLimit A.size A.constant*frameRoof) := by
  let A := ReadyData
  have installed := the_retained_driver_uses_the_one_paid_chart_and_its_printed_bound admitted preparation bytes
  have bootOk := actual_canonical_boot_cut_fits preparation.result.prepared bytes built cut
  obtain ⟨path,bound,_⟩ := actual_exterior_prefix_and_its_live_retained_path_share_one_roof
    admitted.site A.machine admitted.receipt.1 A.first A.exterior on w A.drivers A.valid
    reach ambient entryRoof frameRoof held entry
  exact ⟨installed.1,installed.2.1,path,max_le_max
    (Nat.add_le_add_left bootOk (chartStartupAmbient admitted ambient)) bound⟩

#print axioms chartStartupAmbient
#print axioms actual_paid_chart_and_retained_exterior_path_take_one_named_maximum
end
end J6R116RetainedExteriorPeak

