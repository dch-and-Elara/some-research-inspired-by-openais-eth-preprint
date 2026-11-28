import J6R115RetainedActualChild
import J6R56PrintedExponentLedger

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

open J6R16ModeCost J6R51 J6R56PrintedExponent J6R49Cost J6R24MeteredRecursion

/-- This enumerates occurrences of the installed retained interpreter.
Distinct native addresses remain distinct even if their call payloads
happen to be equal. No such list is allocated during execution. -/
def retainedOccurrencePlan : FinitePlan (KeptInvocation X M) where
  size := fun x=>x.call.edges
  Slot := fun x=>(Plan sel).Slot x.call
  finiteSlot := fun x=>(Plan sel).finiteSlot x.call
  child := fun x w=>retainedActiveChildAt X M D x w.property w
  smaller := fun x w=>retained_actual_child_strictly_decreases X M D x w.property w

def invocationPath (x : KeptInvocation X M) :
    Sigma (Path sel (exteriorChild G ell X.centre X.sample X.group)) :=
  ⟨x.call,.step x.path x.slot⟩

theorem retained_occurrences_follow_the_literal_path_addresses
    {x y : KeptInvocation X M}
    (seen : NativeReach (retainedOccurrencePlan X M D) x y) :
    NativeReach (nativeScopedPlan sel (exteriorChild G ell X.centre X.sample X.group))
      (invocationPath X M x) (invocationPath X M y) := by
  induction seen with
  | reflexive x => exact .reflexive _
  | step w _ ih =>
    exact .step w ih

theorem retained_occurrence_depth_reaches_exact_old_geometric_path
    (x y : KeptInvocation X M) (depth : ℕ)
    (seen : y ∈ occurrences (retainedOccurrencePlan X M D) x depth) :
    NativeReach (nativeScopedPlan sel (exteriorChild G ell X.centre X.sample X.group))
      (invocationPath X M x) (invocationPath X M y) ∧
      y.call.depth=x.call.depth+depth := by
  have ⟨reach,d⟩ := occurrence_reach_depth (retainedOccurrencePlan X M D)
    (fun z=>z.call.depth) (fun _ _=>rfl) x depth y seen
  exact ⟨retained_occurrences_follow_the_literal_path_addresses X M D reach,d⟩

#print axioms retainedOccurrencePlan
#print axioms retained_occurrences_follow_the_literal_path_addresses
#print axioms retained_occurrence_depth_reaches_exact_old_geometric_path
end
end J6R111KeptOwnerFlow

