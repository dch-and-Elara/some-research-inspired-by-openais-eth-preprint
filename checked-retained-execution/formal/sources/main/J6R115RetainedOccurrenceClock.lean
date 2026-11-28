import J6R115RetainedOccurrenceTariff

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

open J6R114RetainedScopeTariff J6R55CachedLedger J6R16ModeCost J6R51 J6R56PrintedExponent

theorem actual_retained_subtree_has_the_original_tapered_clock
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (here : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot))
    (valid : ReadyOnStack (borns M) initial)
    (rootFit : (exteriorChild G ell X.centre X.sample X.group).depth≤pathLimit s C)
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (prec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor (exteriorChild G ell X.centre X.sample X.group))
    (fixed address : ℕ)
    (localCap : ∀ y : KeptInvocation X M,
      y.entry.bank=stackBank (borns M) initial (.step y.path y.slot) →
      retainedOwnTariff X M D retire y initial ≤ fixed+address*Nat.card ((Plan sel).Slot y.call)) :
    (runRetained X M D retire x).steps≤(pathLimit s C-x.call.depth+1)*(fixed+address)*
      2^(fullPrefixConstant C*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) := by
  let P := retainedOccurrencePlan X M D
  let H := pathLimit s C-x.call.depth
  let total := fun y=>(runRetained X M D retire y).steps
  let fee := fun y=>retainedOwnTariff X M D retire y initial
  have bang (j : ℕ) (y : KeptInvocation X M) (seen : y∈occurrences P x j) :
      y.entry.bank=stackBank (borns M) initial (.step y.path y.slot) := by
    have seen' := (occurrence_reach_depth P (fun z=>z.call.depth) (fun _ _=>rfl) x j y seen).1
    exact retained_native_reach_preserves_the_real_published_stack X M D seen' initial here
  have hStep (j : ℕ) (y : KeptInvocation X M) (seen : y∈occurrences P x j) :
      total y ≤ fee y+((childList P y).map total).sum :=
    the_actual_retained_meter_splits_into_real_occurrences X M D retire y initial
      (bang j y seen) (fun {_} p u=>valid p u)
  have finite : occurrences P x (H+1)=[] :=
    no_retained_occurrences_past_the_absolute_depth X M D rootFit x
  have meter := scoped_occurrence_ledger_le P x total fee H hStep finite
  let fan := retained_occurrence_has_the_original_tapered_fanout X M D stable zero prec link x
  have count := total_fee_bound P x s C (Nat.clog 2 s) (siteConstant C)
    (branchBits (Nat.clog 2 s)) (H+1) (fixed+address) fee fan
    (fun j y seen=>local_charge_affine_le (localCap y (bang j y seen)) (fan j y seen))
  apply compress_absolute_meter_bound s C x.call.depth _ _ cfg.constPos cfg.size (root_lambda_large cfg)
  exact meter.trans count

#print axioms actual_retained_subtree_has_the_original_tapered_clock
end
end J6R111KeptOwnerFlow

