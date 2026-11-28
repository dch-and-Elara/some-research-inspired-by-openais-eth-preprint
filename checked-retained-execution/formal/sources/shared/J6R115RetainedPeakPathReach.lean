import J6R115RetainedPeakPathBound
import J6R115RetainedOccurrencePlan

/-! The visits are taken from the very occurrence plan of the
retained evaluator, also used for its exact time ledger. A ready
initial native bank provides a successful same-path scope for each
such visit. No equality to an older runner is used. -/
namespace J6R115RetainedPeakPath
open scoped Polynomial Classical
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
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak
open J6R114RetainedPeak J6R50Peak J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : KeptDrivers X M rank)
variable {start a x : KeptInvocation X M}

theorem observed_retained_path_is_in_the_actual_occurrence_plan
    (path : VisitedRetainedPath X M D start x) :
    NativeReach (retainedOccurrencePlan X M D) start x := by
  induction path with
  | begin=>exact .reflexive _
  | @next parent before on u ok ih=>
    exact nativeReach_trans _ ih (.step u (.reflexive _))

theorem every_ready_actual_retained_reach_has_a_successful_path
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (root : start.entry.bank=stackBank (borns M) initial (.step start.path start.slot))
    (ready : ReadyOnStack (borns M) initial)
    (reach : NativeReach (retainedOccurrencePlan X M D) a x)
    (soFar : VisitedRetainedPath X M D start a) :
    Nonempty (VisitedRetainedPath X M D start x) := by
  induction reach with
  | reflexive => exact ⟨soFar⟩
  | @step b c u tail ih =>
    have legal := original_ready_stack_licenses_the_real_next_observation X M D soFar
      initial root ready u.property u
    exact ih (.next soFar u.property u legal)

/-- A uniform selected path roof from per-invocation field roofs on
the same occurrence plan. The chart remains a single shared field.
The entry cut also applies when the last invocation stops. -/
theorem every_actual_retained_occurrence_has_its_named_peak_on_the_same_tree
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (root : start.entry.bank=stackBank (borns M) initial (.step start.path start.slot))
    (ready : ReadyOnStack (borns M) initial)
    (reach : NativeReach (retainedOccurrencePlan X M D) start x)
    (ambient entryRoof frameRoof : ℕ)
    (held : ∀ {y : KeptInvocation X M},NativeReach (retainedOccurrencePlan X M D) start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof)
    (entry : ∀ {y : KeptInvocation X M},NativeReach (retainedOccurrencePlan X M D) start y→
      invocationEntryBits X M y (chartAndAmbient X M D ambient)≤entryRoof) :
    ∃ path : VisitedRetainedPath X M D start x,
      x.entry.bank=stackBank (borns M) initial (.step x.path x.slot) ∧
      visitedEntryPeak X M D (chartAndAmbient X M D ambient) path≤
        entryRoof+pathLimit s C*frameRoof ∧
      ∀ on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges,
        activeRetainedBits X M D x on (chartAndAmbient X M D ambient)≤entryRoof →
        max (visitedEntryPeak X M D (chartAndAmbient X M D ambient) path)
          (visitedCarry X M D path+activeRetainedBits X M D x on (chartAndAmbient X M D ambient))≤
          entryRoof+pathLimit s C*frameRoof := by
  obtain ⟨path⟩ := every_ready_actual_retained_reach_has_a_successful_path X M D initial root ready reach
    (.begin : VisitedRetainedPath X M D start start)
  have hc : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof :=
    fun p=>held (observed_retained_path_is_in_the_actual_occurrence_plan X M D p)
  have ec : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      invocationEntryBits X M y (chartAndAmbient X M D ambient)≤entryRoof :=
    fun p=>entry (observed_retained_path_is_in_the_actual_occurrence_plan X M D p)
  exact ⟨path,visited_entries_use_the_original_native_stack X M D path initial root,
    retained_path_named_entry_peak_includes_the_one_shared_chart X M D path ambient entryRoof frameRoof hc ec,
    fun on h=>retained_path_named_peak_includes_the_shared_chart_and_current_active_cut X M D path
      ambient entryRoof frameRoof hc ec on h⟩

#print axioms observed_retained_path_is_in_the_actual_occurrence_plan
#print axioms every_ready_actual_retained_reach_has_a_successful_path
#print axioms every_actual_retained_occurrence_has_its_named_peak_on_the_same_tree
end
end J6R115RetainedPeakPath

