import J6R115RetainedPeakPathCut
import J6R50PeakStartPrecision

/-! A proof-side observation along an actual addressed retained path.
It records successful child publications only. An index is the
literal retained child, with its already supplied raw tapes, not a
new run used for comparison. -/
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
set_option maxHeartbeats 16000000
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

inductive VisitedRetainedPath (start : KeptInvocation X M) : KeptInvocation X M→Type 1 where
  | begin : VisitedRetainedPath start start
  | next {x : KeptInvocation X M} (prior : VisitedRetainedPath start x)
      (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
      (u : (Plan sel).Slot x.call)
      (opened : JobsReady x.entry.bank [(retainedActiveChildAt X M D x on u).site.birth.job]) :
      VisitedRetainedPath start (retainedActiveChildAt X M D x on u)

variable {start x : KeptInvocation X M}

/-- The actual normalized slot is the one passed by the sweep at its
centre, probe, mode and group. The active guard is proof-only. -/
theorem retained_visit_uses_the_literal_address (node : KeptInvocation X M)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<node.call.edges)
    (u : (Plan sel).Slot node.call) :
    addressed (sel:=sel) (d:=readyAtPath T (Path.step node.path node.slot) on)
      u.val.1 u.val.2.1 u.val.2.2.1 u.val.2.2.2 = u := by
  obtain ⟨⟨t,z,β,g⟩,fit⟩ := u
  rfl

variable (path : VisitedRetainedPath X M D start x)

def visitedHops : ∀ {x : KeptInvocation X M},VisitedRetainedPath X M D start x→ℕ
  | _, .begin => 0
  | _, .next p _ _ _ => visitedHops p+1

def visitedCarry : ∀ {x : KeptInvocation X M},VisitedRetainedPath X M D start x→ℕ
  | _, .begin => 0
  | _, .next (x:=parent) p _ _ _ => visitedCarry p+suspendedParentBits X M parent

def visitedEntryPeak (shared : ℕ) :
    ∀ {x : KeptInvocation X M},VisitedRetainedPath X M D start x→ℕ
  | _, .begin => invocationEntryBits X M start shared
  | _, .next (x:=parent) p on w _ =>
      max (visitedEntryPeak shared p)
        (visitedCarry X M D p+activeChildCutBits X M D parent on w shared)

include path in
theorem visited_entries_use_the_original_native_stack
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (root : start.entry.bank=stackBank (borns M) initial (.step start.path start.slot)) :
    x.entry.bank=stackBank (borns M) initial (.step x.path x.slot) := by
  induction path with
  | begin=>exact root
  | @next y prior on u opened ih=>
    exact retained_actual_child_has_the_exact_kept_stack X M D y on u initial ih

include path in
theorem original_ready_stack_licenses_the_real_next_observation
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (root : start.entry.bank=stackBank (borns M) initial (.step start.path start.slot))
    (valid : ReadyOnStack (borns M) initial)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges) (u : (Plan sel).Slot x.call) :
    JobsReady x.entry.bank [(retainedActiveChildAt X M D x on u).site.birth.job] := by
  let child := retainedActiveChildAt X M D x on u
  change JobsReady x.entry.bank [child.site.birth.job]
  rw [child.actualSite,visited_entries_use_the_original_native_stack X M D path initial root]
  exact valid (.step x.path x.slot) u

theorem visited_hops_preserve_the_absolute_native_depth :
    moves (Path.step start.path start.slot) + visitedHops X M D path =
      moves (Path.step x.path x.slot) := by
  induction path with
  | begin=>simp only [visitedHops,Nat.add_zero]
  | @next y prior on u opened ih=>
    change moves (Path.step start.path start.slot)+(visitedHops X M D prior+1)=
      moves (Path.step y.path y.slot)+1
    rw [←Nat.add_assoc,ih]

theorem visited_hops_fit_the_printed_path_limit :
    visitedHops X M D path≤pathLimit s C := by
  have exact := visited_hops_preserve_the_absolute_native_depth X M D path
  have roof := actual_ancestry_moves_any_start cfg sel T.rootStable (Path.step x.path x.slot)
  omega

theorem current_live_entry_and_its_ancestors_are_in_the_observed_peak (shared : ℕ) :
    visitedCarry X M D path+invocationEntryBits X M x shared≤
      visitedEntryPeak X M D shared path := by
  cases path with
  | begin=>simp only [visitedCarry,visitedEntryPeak,Nat.zero_add,le_refl]
  | @next y prior on u opened=>
    change (visitedCarry X M D prior+suspendedParentBits X M y)+
      invocationEntryBits X M (retainedActiveChildAt X M D y on u) shared≤
      max (visitedEntryPeak X M D shared prior) (visitedCarry X M D prior+activeChildCutBits X M D y on u shared)
    rw [Nat.add_assoc,←exact_child_cut_is_suspended_parent_plus_that_child_entry X M D y on u shared]
    exact Nat.le_max_right _ _

#print axioms VisitedRetainedPath
#print axioms retained_visit_uses_the_literal_address
#print axioms visited_entries_use_the_original_native_stack
#print axioms original_ready_stack_licenses_the_real_next_observation
#print axioms visited_hops_preserve_the_absolute_native_depth
#print axioms visited_hops_fit_the_printed_path_limit
#print axioms current_live_entry_and_its_ancestors_are_in_the_observed_peak
end
end J6R115RetainedPeakPath

