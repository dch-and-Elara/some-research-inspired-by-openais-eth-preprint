import J6R115RetainedPeakPathTrace

/-! A high-water mark of the selected live payloads on the same
retained path. The local roofs are explicit, for only these fields.
There is no full allocator bound or peak bound for another runner. -/
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
set_option maxHeartbeats 13000000
set_option maxRecDepth 4700
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
variable {start x : KeptInvocation X M}
variable (path : VisitedRetainedPath X M D start x)

def chartAndAmbient (ambient : ℕ) : ℕ :=
  ambient+gridMemoryBits D.masks.table.raw

theorem each_suspension_contributes_once_to_the_visited_peak
    (shared entryRoof frameRoof : ℕ)
    (held : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof)
    (entry : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      invocationEntryBits X M y shared≤entryRoof) :
    visitedCarry X M D path≤visitedHops X M D path*frameRoof ∧
    visitedEntryPeak X M D shared path≤entryRoof+visitedHops X M D path*frameRoof := by
  induction path with
  | begin =>
    simp only [visitedCarry,visitedEntryPeak,visitedHops,Nat.zero_mul,Nat.add_zero,le_refl,true_and]
    exact entry (.begin : VisitedRetainedPath X M D start start)
  | @next y p on u ready ih =>
    let more : VisitedRetainedPath X M D start (retainedActiveChildAt X M D y on u) := .next p on u ready
    have carry : visitedCarry X M D more≤visitedHops X M D more*frameRoof := by
      change visitedCarry X M D p+suspendedParentBits X M y≤(visitedHops X M D p+1)*frameRoof
      rw [Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add ih.1 (held p on)
    refine ⟨carry,max_le ?_ ?_⟩
    · exact ih.2.trans (Nat.add_le_add_left
          (Nat.mul_le_mul_right frameRoof (Nat.le_succ _)) entryRoof)
    · rw [exact_child_cut_is_suspended_parent_plus_that_child_entry X M D y on u shared,←Nat.add_assoc]
      exact (Nat.add_le_add carry (entry more)).trans (Nat.add_comm _ _).le

/-- The chosen chart is a single ambient field of this same run. We
sum only the disjoint ancestor roles at each cut, then take a maximum
of cuts. The active stop at the end of the observed prefix can be
included separately; the caller supplies its actual named cap. -/
theorem retained_path_named_peak_includes_the_shared_chart_and_current_active_cut
    (ambient entryRoof frameRoof : ℕ)
    (held : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof)
    (entry : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      invocationEntryBits X M y (chartAndAmbient X M D ambient)≤entryRoof)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (active : activeRetainedBits X M D x on (chartAndAmbient X M D ambient)≤entryRoof) :
    max (visitedEntryPeak X M D (chartAndAmbient X M D ambient) path)
      (visitedCarry X M D path+activeRetainedBits X M D x on (chartAndAmbient X M D ambient))≤
      entryRoof+pathLimit s C*frameRoof := by
  let shared := chartAndAmbient X M D ambient
  have bounded := each_suspension_contributes_once_to_the_visited_peak X M D path shared
    entryRoof frameRoof held entry
  have hops := Nat.mul_le_mul_right frameRoof (visited_hops_fit_the_printed_path_limit X M D path)
  have endBound := (Nat.add_le_add bounded.1 active).trans (Nat.add_comm _ _).le
  exact (max_le bounded.2 endBound).trans (Nat.add_le_add_left hops entryRoof)

theorem retained_path_named_entry_peak_includes_the_one_shared_chart
    (ambient entryRoof frameRoof : ℕ)
    (held : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      (printedParams (f:=f) (ell:=ell) s).cutoff<y.call.edges→suspendedParentBits X M y≤frameRoof)
    (entry : ∀ {y : KeptInvocation X M},VisitedRetainedPath X M D start y→
      invocationEntryBits X M y (chartAndAmbient X M D ambient)≤entryRoof) :
    visitedEntryPeak X M D (chartAndAmbient X M D ambient) path≤
      entryRoof+pathLimit s C*frameRoof :=
  (each_suspension_contributes_once_to_the_visited_peak X M D path _ entryRoof frameRoof held entry).2.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right frameRoof (visited_hops_fit_the_printed_path_limit X M D path)) entryRoof)

#print axioms chartAndAmbient
#print axioms each_suspension_contributes_once_to_the_visited_peak
#print axioms retained_path_named_peak_includes_the_shared_chart_and_current_active_cut
#print axioms retained_path_named_entry_peak_includes_the_one_shared_chart
end
end J6R115RetainedPeakPath

