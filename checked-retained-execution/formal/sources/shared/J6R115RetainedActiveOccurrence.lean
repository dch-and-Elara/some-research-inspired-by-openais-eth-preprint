import J6R115RetainedActualChild
import J6R114RetainedActiveClock

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
set_option maxHeartbeats 3600000
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


def actualRetainedChildScopeDebit
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (u : (@Plan f ell s sel).Slot x.call) : Nat :=
  let path : Path sel (exteriorChild G ell X.centre X.sample X.group) x.call := .step x.path x.slot
  let heads := readGroupHeadersForActive X x.path x.slot x.site x.entry
  cachedScopeOwn (cfg:=cfg) (sel:=sel) (T:=T) (c:=x.call) M retire initial path u +
    keptSuccessorOwnerScan X x.path x.slot x.site x.entry heads.result

def actualRetainedActiveLocalPrefix
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges) : Nat :=
  let path : Path sel (exteriorChild G ell X.centre X.sample X.group) x.call := .step x.path x.slot
  let checked := readyAtPath T path on
  let heads := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let chosen := D.layout x on heads.result
  let layout := selectedLayoutAndLabels chosen.setup
  let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
    (D.fit path on) D.masks layout.steps
  let cache := mountResident x.site x.entry.resident
  let tariff := @streamActiveTariff f ell s sel x.call checked T.bank rate A.result.proofView
    (reachable_positive T path.reached) T.vPositive
  heads.steps+cache.steps+A.steps+tariff

theorem retained_active_clock_sums_the_actual_physical_children
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (bank : x.entry.bank=stackBank (borns M) initial (.step x.path x.slot))
    (valid : ReadyOnStack (borns M) initial)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges) :
    letI : Fintype ((@Plan f ell s sel).Slot x.call) := (@Plan f ell s sel).finiteSlot x.call
    (runRetained X M D retire x).steps ≤ actualRetainedActiveLocalPrefix X M D x on +
      (∑ u : (@Plan f ell s sel).Slot x.call,
        ((runRetained X M D retire (retainedActiveChildAt X M D x on u)).steps +
         actualRetainedChildScopeDebit X M retire x initial u)) := by
  let sp := printedParams (f:=f) (ell:=ell) s
  let current : Call (PhysicalHost f ell) := x.call
  let path : Path sel (exteriorChild G ell X.centre X.sample X.group) current := Path.step x.path x.slot
  let d := readyAtPath T path on
  let heads := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let W := D.layout x on heads.result
  let layout := selectedLayoutAndLabels W.setup
  let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
    (D.fit path on) D.masks layout.steps
  let cache := mountResident x.site x.entry.resident
  let scope (u : (Plan sel).Slot current) :=
    retainActualSelectedDemand X x.path x.slot x.site x.entry M u heads.result
  let keys (u : (Plan sel).Slot current) := actual_live_keys_at_the_selected_site X M D x u
  let labels (u : (Plan sel).Slot current) :=
    checkedChildLabelWords X x.path x.slot x.site x.entry M on heads.result
      W u cache.result (keys u) layout.result rfl
  let same (u : (Plan sel).Slot current) :=
    selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
      x.entry M u heads.result cache.result x.actualSite
  let resume (u : (Plan sel).Slot current) (entry : CapturedEntry X path u
      (produceCacheSidecarOnce (scope u).result.load cache.result).result.next) :
      InvocationOut X M ⟨current,path,u,_,same u,entry⟩ :=
    runRetained X M D retire ⟨current,path,u,_,same u,entry⟩
  let read : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
    let u := addressed (sel:=sel) d t z β g
    project (nextR66OwnerScope X x.path x.slot x.site u (scope u) cache.result (keys u) retire
      (labels u) (resume u)
      (zeroM (T.bank (registerPrecision sp current t) (register_positive d t)).hp) x.entry.bank)
  let charge (u : (Plan sel).Slot current) :=
    (runRetained X M D retire (retainedActiveChildAt X M D x on u)).steps+
    actualRetainedChildScopeDebit X M retire x initial u
  letI : Fintype ((Plan sel).Slot current) := (Plan sel).finiteSlot current
  have bills : (@streamActiveChildBill f ell s sel current d T.bank rate A.result.proofView read) =
      ∑ u : (Plan sel).Slot current,charge u := by
    apply stream_active_child_bill_matches_slots A.result.proofView T.vPositive read charge
    intro t z β g
    let w := addressed (sel:=sel) d t z β g
    let low := T.bank (registerPrecision sp current t) (register_positive d t)
    let bad : Meter (Block low ell) := zeroM low.hp
    have measured := (actual_kept_child_scope_preserves_parent_and_pays_one_owner_scan (Out:=Block low ell)
      X x.path x.slot x.site x.entry M w heads.result cache.result (keys w) retire x.entry.bank
      initial (labels w) (resume w) bad x.actualSite bank (fun {_} p w=>valid p w)).2
    change (read t z β g).steps =
      (runRetained X M D retire (retainedActiveChildAt X M D x on w)).steps+
        (cachedScopeOwn M retire initial path w+
          keptSuccessorOwnerScan X x.path x.slot x.site x.entry heads.result)
    rw [←Nat.add_assoc]
    exact measured
  have paid := retained_active_paid_on_its_own_execution X M D retire x on
  change (runRetained X M D retire x).steps≤heads.steps+cache.steps+A.steps+
    ((@streamActiveChildBill f ell s sel current d T.bank rate A.result.proofView read)+
      (@streamActiveTariff f ell s sel current d T.bank rate A.result.proofView) (reachable_positive T path.reached) T.vPositive) at paid
  rw [bills] at paid
  change (runRetained X M D retire x).steps ≤
    heads.steps+cache.steps+A.steps +
      (@streamActiveTariff f ell s sel current d T.bank rate A.result.proofView
        (reachable_positive T path.reached) T.vPositive) + (∑ u, charge u)
  omega

#print axioms retained_active_clock_sums_the_actual_physical_children
end
end J6R111KeptOwnerFlow

