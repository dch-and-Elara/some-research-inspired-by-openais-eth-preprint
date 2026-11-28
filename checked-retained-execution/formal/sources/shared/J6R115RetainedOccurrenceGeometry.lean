import J6R115RetainedOccurrencePlan

/-! The tariff is attached directly to the current retained execution,
including its own label/header pass and its own recursive calls. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial BigOperators
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
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R49Cost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 5300
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
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (x : KeptInvocation X M)

open J6R16ModeCost J6R51 J6R56PrintedExponent J6R49Cost J6R50Integration

theorem retained_native_reach_preserves_the_real_published_stack
    {start last : KeptInvocation X M}
    (seen : NativeReach (retainedOccurrencePlan X M D) start last)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (here : start.entry.bank=stackBank (borns M) initial (.step start.path start.slot)) :
    last.entry.bank=stackBank (borns M) initial (.step last.path last.slot) := by
  induction seen with
  | reflexive => exact here
  | step u _ ih =>
    exact ih (retained_actual_child_has_the_exact_kept_stack X M D _ u.property u initial here)

theorem retained_at_actual_root_has_bounded_absolute_depth
    (rootFit : (exteriorChild G ell X.centre X.sample X.group).depth≤pathLimit s C)
    (z : KeptInvocation X M) : z.call.depth≤pathLimit s C :=
  stable_path_depth_bound_from_start cfg sel (Path.step z.path z.slot).reached T.rootStable rootFit

theorem no_retained_occurrences_past_the_absolute_depth
    (rootFit : (exteriorChild G ell X.centre X.sample X.group).depth≤pathLimit s C)
    (x : KeptInvocation X M) :
    occurrences (retainedOccurrencePlan X M D) x (pathLimit s C-x.call.depth+1)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro z inList
  have h := (retained_occurrence_depth_reaches_exact_old_geometric_path X M D x z _ inList).2
  have hz := retained_at_actual_root_has_bounded_absolute_depth X M rootFit z
  omega

theorem retained_occurrence_has_the_original_tapered_fanout
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (prec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor (exteriorChild G ell X.centre X.sample X.group))
    (x : KeptInvocation X M) (j : ℕ) (z : KeptInvocation X M)
    (seen : z∈occurrences (retainedOccurrencePlan X M D) x j) :
    Nat.card ((retainedOccurrencePlan X M D).Slot z)≤2^
      (branchBits (Nat.clog 2 s)+depthExponent s C (Nat.clog 2 s) (siteConstant C) j) := by
  let L := Nat.clog 2 s
  have absReach := nativeReach_trans (Plan sel) link (Path.step z.path z.slot).reached
  have dep := (retained_occurrence_depth_reaches_exact_old_geometric_path X M D x z j seen).2
  exact (live_addresses_bound cfg sel absReach stable zero prec).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
      (depth_exponent_antitone s C L (siteConstant C) (show j≤z.call.depth by omega)) _))

#print axioms retained_native_reach_preserves_the_real_published_stack
#print axioms no_retained_occurrences_past_the_absolute_depth
#print axioms retained_occurrence_has_the_original_tapered_fanout
end
end J6R111KeptOwnerFlow

