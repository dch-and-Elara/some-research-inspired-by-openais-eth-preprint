import J6R111KeptOwnerFlowRunSetup
import J6R111KeptOwnerFlowStop
import J6R68ActiveInputsSweepRun

/-! Retain the complete source operands in the actual recursive argument
of the R66/R68 evaluator. The chosen original demand still runs at each
visited address; it is not looked up in any precomputed tree. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
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
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 5750
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)

structure KeptInvocation where
  parent : Call (PhysicalHost f ell)
  path : Path sel (exteriorChild G ell X.centre X.sample X.group) parent
  slot : (Plan sel).Slot parent
  site : StoredSite T (path.ticket slot) key prec tw bw (pageKeyWidth m+pad)
  actualSite : site=sourceState M path slot
  entry : CapturedEntry X path slot site

abbrev KeptInvocation.call (x : KeptInvocation X M) := (Plan sel).child x.parent x.slot

abbrev InvocationOut (x : KeptInvocation X M) :=
  Meter (Block (T.frame (Path.step x.path x.slot).reached) ell×PageBank f ell key prec tw bw (pageKeyWidth m+pad))

/-- The original machine, actual mounted mask chart, and selected current
layout are used. The new guard is exactly ownership-name context
compatibility for the fixed request's actual published successor. -/
structure KeptDrivers (rank : ℕ) where
  masks : MountedChart T
  fit : ∀ {c : Call (PhysicalHost f ell)} (path : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges), InputFits sel (readyAtPath T path on) rate
  layout : ∀ (x : KeptInvocation X M)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (H : ParentOwnerHeaders x.site.site), SelectedOwnerLayout X x.path x.slot x.site x.entry on H rank
  names : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
    (w : (Plan sel).Slot c) (u : (Plan sel).Slot (p.ticket w).child),
    NativeCreationOwnerContext (sourceState M p w) (M.demand (sourceState M p w) u).result

variable {rank : ℕ} (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (x : KeptInvocation X M)

include D in
theorem actual_live_keys_at_the_selected_site (u : (Plan sel).Slot (x.path.ticket x.slot).child) :
    NativeCreationOwnerContext x.site (M.demand x.site u).result := by
  rw [x.actualSite]
  exact D.names x.path x.slot u

/-- Same R68 active sweep, but carry all three measured source operands
inside the recursive call. The header/label pass is made once at this
active parent; the real selected demand and the explicit owner scan
are executed once per addressed child. -/
def retainedBody
    (recur : (y : KeptInvocation X M)→y.call.edges<x.call.edges→InvocationOut X M y) :
    InvocationOut X M x :=
  let sp := printedParams (f:=f) (ell:=ell) s
  let current := x.call
  let path := Path.step x.path x.slot
  if stop : current.edges≤sp.cutoff then
    if current.edges=0 then
      let old := M.leafAfter x.path x.slot x.site stop x.entry.bank
      ⟨(old.result,x.entry.bank),old.steps⟩
    else
      resumePositive X x.path x.slot x.site x.entry
  else
    let on := Nat.lt_of_not_ge stop
    let checked := readyAtPath T path on
    let incumbent := readGroupHeadersForActive X x.path x.slot x.site x.entry
    let W := D.layout x on incumbent.result
    let layout := selectedLayoutAndLabels W.setup
    let plan := prepareFromKeptLayout X x.path x.slot x.site x.entry M on layout.result
      (D.fit path on) D.masks layout.steps
    let mounted := mountResident x.site x.entry.resident
    let out := plan.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive X.hf
      (fun t z β g=>
        let u := addressed (sel:=sel) checked t z β g
        let K := retainActualSelectedDemand X x.path x.slot x.site x.entry M u incumbent.result
        let keys := actual_live_keys_at_the_selected_site X M D x u
        let childLabels := checkedChildLabelWords X x.path x.slot x.site x.entry M on incumbent.result
          W u mounted.result keys layout.result rfl
        let same := selected_load_emits_the_actual_driver_source_after_retention X x.path x.slot x.site
          x.entry M u incumbent.result mounted.result x.actualSite
        project (nextR66OwnerScope X x.path x.slot x.site u K mounted.result keys retire childLabels
          (fun entered=>
            recur ⟨current,path,u,_,same,entered⟩ ((Plan sel).smaller current u))
          (zeroM (T.bank (registerPrecision sp current t) (register_positive checked t)).hp) x.entry.bank))
    ⟨(out.result,x.entry.bank),incumbent.steps+mounted.steps+plan.steps+out.steps⟩

def runRetained : InvocationOut X M x :=
  (measure (fun a : KeptInvocation X M=>a.call.edges)).wf.fix (retainedBody X M D retire) x

theorem run_retained_unfolds_to_the_actual_child_callback :
    runRetained X M D retire x=retainedBody X M D retire x (fun y _=>runRetained X M D retire y) :=
  WellFounded.fix_eq _ _ _

theorem retained_runner_uses_the_live_positive_leaf_without_a_provider
    (stop : x.call.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<x.call.edges) :
    runRetained X M D retire x=resumePositive X x.path x.slot x.site x.entry := by
  rw [run_retained_unfolds_to_the_actual_child_callback]
  simp only [retainedBody,dif_pos stop,if_neg (Nat.ne_of_gt positive)]

theorem retained_runner_restores_its_own_directory :
    (runRetained X M D retire x).result.2=x.entry.bank := by
  rw [run_retained_unfolds_to_the_actual_child_callback]
  by_cases stop : x.call.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff
  · by_cases zero : x.call.edges=0
    · simp only [retainedBody,dif_pos stop,if_pos zero]
    · simp only [retainedBody,dif_pos stop,if_neg zero,resumePositive]
  · simp only [retainedBody,dif_neg stop]

#print axioms retainedBody
#print axioms run_retained_unfolds_to_the_actual_child_callback
#print axioms retained_runner_uses_the_live_positive_leaf_without_a_provider
#print axioms retained_runner_restores_its_own_directory
end
end J6R111KeptOwnerFlow

