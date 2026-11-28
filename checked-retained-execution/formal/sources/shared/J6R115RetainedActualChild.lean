import J6R111KeptOwnerFlowRun
import J6R49CostActive
import J6R114RetainedScopeTariffExact

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

open J6R114RetainedScopeTariff J6R55CachedLedger

/-- Exact proof-side view of the descriptor already consumed by the actual
retained parent. Used to index the native occurrence ledger, not executed
as a second child preparation. -/
def retainedActiveChildAt
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (u : (Plan sel).Slot x.call) : KeptInvocation X M :=
  let path := Path.step x.path x.slot
  let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let W := D.layout x on H.result
  let layout := selectedLayoutAndLabels W.setup
  let cache := mountResident x.site x.entry.resident
  let K := retainActualSelectedDemand X x.path x.slot x.site x.entry M u H.result
  let keys := actual_live_keys_at_the_selected_site X M D x u
  let labels := checkedChildLabelWords X x.path x.slot x.site x.entry M on H.result
    W u cache.result keys layout.result rfl
  let N := (produceCacheSidecarOnce K.result.load cache.result).result.next
  let same := selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
    x.entry M u H.result cache.result x.actualSite
  let owners := carriedRosterAtEmission X x.path x.slot x.site u K cache.result keys
  let born := installResidentBank N
  let entry : CapturedEntry X path u N :=
    ⟨born.result,afterOne x.entry.bank N.birth.job,rfl,owners,labels⟩
  ⟨x.call,path,u,N,same,entry⟩

theorem retained_actual_child_strictly_decreases
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (u : (Plan sel).Slot x.call) :
    (retainedActiveChildAt X M D x on u).call.edges<x.call.edges :=
  (Plan sel).smaller x.call u

theorem retained_actual_child_has_the_exact_kept_stack
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (u : (Plan sel).Slot x.call)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (here : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot)) :
    (retainedActiveChildAt X M D x on u).entry.bank =
      stackBank (borns M) initial (.step (.step x.path x.slot) u) := by
  let arg := retainedActiveChildAt X M D x on u
  change afterOne x.entry.bank arg.site.birth.job=_
  rw [arg.actualSite,here]
  rfl

#print axioms retainedActiveChildAt
#print axioms retained_actual_child_strictly_decreases
#print axioms retained_actual_child_has_the_exact_kept_stack
end
end J6R111KeptOwnerFlow

