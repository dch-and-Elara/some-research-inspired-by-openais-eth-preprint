import J6R115RetainedActiveOccurrence
import J6R115RetainedOccurrenceGeometry

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

variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

/-- Nonrecursive charges of the exact retained invocation. The leaf branch
is the actual terminal invocation; at active nodes only the physical
setup and each actual successor's ingress/retirement enter this bill. -/
def retainedOwnTariff : ℕ :=
  if on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges then
    let path := Path.step x.path x.slot
    let heads := readGroupHeadersForActive X x.path x.slot x.site x.entry
    let W := D.layout x on heads.result
    let layout := selectedLayoutAndLabels W.setup
    let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
      (D.fit path on) D.masks layout.steps
    let resident := mountResident x.site x.entry.resident
    letI : Fintype ((Plan sel).Slot x.call) := (Plan sel).finiteSlot x.call
    heads.steps+resident.steps+A.steps+
    streamActiveTariff A.result.proofView (reachable_positive T path.reached) T.vPositive+
      ∑ u : (Plan sel).Slot x.call,
        (cachedScopeOwn M retire initial path u+
          keptSuccessorOwnerScan X x.path x.slot x.site x.entry heads.result)
  else (runRetained X M D retire x).steps

theorem the_actual_retained_meter_splits_into_real_occurrences
    (here : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot))
    (valid : ReadyOnStack (borns M) initial) :
    (runRetained X M D retire x).steps≤retainedOwnTariff X M D retire x initial+
      ((childList (retainedOccurrencePlan X M D) x).map
        (fun y=>(runRetained X M D retire y).steps)).sum := by
  classical
  let P := retainedOccurrencePlan X M D
  by_cases on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges
  · let path := Path.step x.path x.slot
    let heads := readGroupHeadersForActive X x.path x.slot x.site x.entry
    let W := D.layout x on heads.result
    let layout := selectedLayoutAndLabels W.setup
    let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
      (D.fit path on) D.masks layout.steps
    let resident := mountResident x.site x.entry.resident
    let base := heads.steps+resident.steps+A.steps
    let overhead := streamActiveTariff A.result.proofView (reachable_positive T path.reached) T.vPositive
    let visit := fun u : (Plan sel).Slot x.call=>
      cachedScopeOwn M retire initial path u+
        keptSuccessorOwnerScan X x.path x.slot x.site x.entry heads.result
    let child := fun u : (Plan sel).Slot x.call=>
      (runRetained X M D retire (P.child x u)).steps
    letI : Fintype ((Plan sel).Slot x.call) := (Plan sel).finiteSlot x.call
    have actual := retained_active_clock_sums_the_actual_physical_children X M D retire x
      initial here (fun {_} p u=>valid p u) on
    change (runRetained X M D retire x).steps≤
      base+overhead+(∑ u, (child u+visit u)) at actual
    rw [Finset.sum_add_distrib] at actual
    rw [retainedOwnTariff,dif_pos on]
    change (runRetained X M D retire x).steps≤base+overhead+(∑ u,visit u)+
      ((childList P x).map (fun y=>(runRetained X M D retire y).steps)).sum
    have entry := childList_bill_as_sum P x (fun y=>(runRetained X M D retire y).steps)
    change (((childList P x).map (fun y=>(runRetained X M D retire y).steps)).sum)=(∑ u,child u) at entry
    rw [entry]
    omega
  · rw [retainedOwnTariff,dif_neg on]
    exact Nat.le_add_right _ _

#print axioms retainedOwnTariff
#print axioms the_actual_retained_meter_splits_into_real_occurrences
end
end J6R111KeptOwnerFlow

