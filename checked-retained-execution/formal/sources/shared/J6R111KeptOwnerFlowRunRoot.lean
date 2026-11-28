import J6R111KeptOwnerFlowRun
import J6R111KeptOwnerFlowLiteralFirst
import J6R66ActiveExterior

/-! Start the retained continuation at the real first physical slot.
The already published exterior is read, not installed again. -/
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
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R68.RecursivePeak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29500000
set_option maxRecDepth 5500
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
local instance rootFlowEdgeRunRoot : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
  (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge


variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (head : OwnsHeader X.header.result initial)

/-- Executable first-slot source. The configured R108 instance is the
prior exact `configuredFirstWithOwners` receipt. -/
structure FirstSource where
  make : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
    Meter (FirstSlotWithOwners (pad:=pad) (T:=T) X w)
  exact : ∀ w, let S := make w
    (⟨S.result.site,S.steps⟩ : Meter (StoredSite T ((Path.root :
      Path sel (exteriorChild G ell X.centre X.sample X.group)
        (exteriorChild G ell X.centre X.sample X.group)).ticket w)
          key prec tw bw (pageKeyWidth m+pad)))=M.initial w

variable (boot : FirstSource X M)

structure ExteriorLabels (rank : ℕ) where
  setup : ∀ on : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges,
    ChosenSetup (c:=(exteriorChild G ell X.centre X.sample X.group)) sel
      (readyAtPath T (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
        (exteriorChild G ell X.centre X.sample X.group)) on) rank
  order : ∀ (on) w, (boot.make w).result.owners.order=(setup on).input.order
  exactLabels : ∀ on, (setup on).input.run.result.2=(setup on).input.order.map (fun v=>
    (setup on).input.format.label (wordsOf (packing sel (readyAtPath T (Path.root :
      Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)) on)) v))

variable {rank : ℕ} (D : KeptDrivers X M rank) (E : ExteriorLabels X M boot rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)

section OneBoot
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
variable (started : Meter (FirstSlotWithOwners (pad:=pad) (T:=T) X w)) {Out : Type}
variable (go : CapturedEntry X
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
  w started.result.site→Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (labels : LabelWitness X
  (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
  w started.result.site started.result.owners)
variable (bad : Meter Out)

def enterPaidFirst : Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let out := withScopeHeader retire started.result.site.birth.job (fun B owner=>
    let R := installResidentBank started.result.site
    let result := go ⟨R.result,B,owner,started.result.owners,labels⟩
    ⟨result.result,R.steps+result.steps⟩) bad initial
  ⟨out.result,started.steps+out.steps⟩

theorem the_paid_first_carrier_enters_one_live_resident_and_restores_parent
    (legal : JobsReady initial [started.result.site.birth.job]) :
    let next := started.result.site
    let j := next.birth.job
    let R := installResidentBank next
    let child := go ⟨R.result,afterOne initial j,rfl,started.result.owners,labels⟩
    enterPaidFirst X initial retire w started go labels bad=
      ⟨(child.result.1,initial),started.steps+
        (publishFee initial j.entry j.offset j.built+(R.steps+child.steps)+retire j+4)⟩ := by
  unfold enterPaidFirst
  dsimp only
  rw [the_actual_header_scope_enters_its_published_head _ _ _ _ _ legal]
end OneBoot

def runRetainedExterior :
    Meter (Block (T.frame (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
      (exteriorChild G ell X.centre X.sample X.group)).reached) ell×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let sp := printedParams (f:=f) (ell:=ell) s
  let path : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group) := .root
  if stop : (exteriorChild G ell X.centre X.sample X.group).edges≤sp.cutoff then
    let done := M.leafRoot stop initial
    ⟨(done.result,initial),done.steps⟩
  else
    let on := Nat.lt_of_not_ge stop
    let d := readyAtPath T path on
    let W := E.setup on
    let packed := selectedLayoutAndLabels W
    let taper := actual_path_taper T path on
    let A := prepare (bank:=T.bank) M.modeWidth (D.fit path on) taper.1 taper.2 X.hf
      D.masks.table (D.masks.covers path on) (readExterior X initial head) ⟨packed.result.receipt,packed.steps⟩
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive X.hf
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        let start := boot.make w
        let agree : start.result.site=sourceState M path w := congrArg Meter.result (boot.exact w)
        let labels := useAlreadyEmittedLabels X path w start.result.site start.result.owners W packed.result rfl
          start.result.injective (E.order on w) (E.exactLabels on)
        project (enterPaidFirst X initial retire w start
          (fun entry=>runRetained X M D retire ⟨exteriorChild G ell X.centre X.sample X.group,path,w,_,agree,entry⟩)
          labels (zeroM (T.bank (registerPrecision sp (exteriorChild G ell X.centre X.sample X.group) t)
            (register_positive d t)).hp)))
    ⟨(out.result,initial),A.steps+out.steps⟩

theorem retained_exterior_returns_the_actual_original_bank :
    (runRetainedExterior X M initial head boot D E retire).result.2=initial := by
  by_cases stop : (exteriorChild G ell X.centre X.sample X.group).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff
  · simp only [runRetainedExterior,dif_pos stop]
  · simp only [runRetainedExterior,dif_neg stop]

#print axioms the_paid_first_carrier_enters_one_live_resident_and_restores_parent
#print axioms runRetainedExterior
#print axioms retained_exterior_returns_the_actual_original_bank
end
end J6R111KeptOwnerFlow

