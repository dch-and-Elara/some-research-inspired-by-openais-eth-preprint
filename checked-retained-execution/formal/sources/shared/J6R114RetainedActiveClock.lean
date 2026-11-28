import J6R111KeptOwnerFlowRun
import J6R49CostActive

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

theorem retained_active_paid_on_its_own_execution
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges) :
    let sp := printedParams (f:=f) (ell:=ell) s
    let current := x.call
    let path := Path.step x.path x.slot
    let checked := readyAtPath T path on
    let incumbent := readGroupHeadersForActive X x.path x.slot x.site x.entry
    let W := D.layout x on incumbent.result
    let layout := selectedLayoutAndLabels W.setup
    let plan := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
      (D.fit path on) D.masks layout.steps
    let mounted := mountResident x.site x.entry.resident
    let read : ActiveChild (sel:=sel) (d:=checked) T.bank := fun t z β g=>
      let u := addressed (sel:=sel) checked t z β g
      let K := retainActualSelectedDemand X x.path x.slot x.site x.entry M u incumbent.result
      let keys := actual_live_keys_at_the_selected_site X M D x u
      let childLabels := checkedChildLabelWords X x.path x.slot x.site x.entry M on incumbent.result
        W u mounted.result keys layout.result rfl
      let same := selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
        x.entry M u incumbent.result mounted.result x.actualSite
      project (nextR66OwnerScope X x.path x.slot x.site u K mounted.result keys retire childLabels
        (fun entered=>runRetained X M D retire ⟨current,path,u,_,same,entered⟩)
        (zeroM (T.bank (registerPrecision sp current t) (register_positive checked t)).hp) x.entry.bank)
    (runRetained X M D retire x).steps ≤ incumbent.steps+mounted.steps+plan.steps+
      (streamActiveChildBill plan.result.proofView read+
        streamActiveTariff plan.result.proofView (reachable_positive T path.reached) T.vPositive) := by
  dsimp only
  let p := Path.step x.path x.slot
  have hs := (stable_reachable cfg sel p.reached T.rootStable).sizeByDepth
  obtain ⟨hu,_,huM⟩ := printed_taper_legal s x.call.edges C x.call.depth
    cfg.widthPos cfg.constPos cfg.size on hs
  rw [run_retained_unfolds_to_the_actual_child_callback,retainedBody,dif_neg (Nat.not_le.mpr on)]
  dsimp only
  rw [Schedule.exact_sweep_matches_its_own_proof_view]
  apply Nat.add_le_add_left
  apply actual_stream_active_word_meter _ M.modeWidth _ T.vPositive X.hf hu huM

#print axioms retained_active_paid_on_its_own_execution
end
end J6R111KeptOwnerFlow

