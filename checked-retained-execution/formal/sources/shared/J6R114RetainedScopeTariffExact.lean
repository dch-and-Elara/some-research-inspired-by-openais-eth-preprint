import J6R114RetainedScopeTariffBase

/-! Exact fee of the already executed retained successor. Its local
ordinary scope debit is shared with the old accounting *formula*, not
an alternative execution or legacy recursive callback. -/
namespace J6R114RetainedScopeTariff
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R82LayoutDebit V8NativeMessage.N2DLabels
open J6R111KeptOwnerFlow J6R55CachedLedger J6R53PeakAddon J6R49Cost
open J6R48GeneratedAddons J6R68.RecursivePeak J6R52CacheSource J6R57ScopeFee
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000000
set_option maxRecDepth 5450
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (H : ParentOwnerHeaders Y.site)

variable (cache : CachedParentFrames Y.site)
variable (keys : NativeCreationOwnerContext Y (M.demand Y u).result)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (B initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable {Out : Type}
variable (labels : let K := retainActualSelectedDemand X p w Y A M u H
  LabelWitness X (.step p w) u (produceCacheSidecarOnce K.result.load cache).result.next
    (carriedRosterAtEmission X p w Y u K cache keys))
variable (resume : CapturedEntry X (.step p w) u
    (produceCacheSidecarOnce (retainActualSelectedDemand X p w Y A M u H).result.load cache).result.next →
      Meter (Out×PageBank f ell key prec tw bw (pageKeyWidth m+pad)))
variable (bad : Meter Out)

theorem actual_kept_child_scope_preserves_parent_and_pays_one_owner_scan
    (here : Y=sourceState M p w)
    (onBank : B=stackBank (borns M) initial (.step p w))
    (legal : ReadyOnStack (borns M) initial) :
    let K := retainActualSelectedDemand X p w Y A M u H
    let N := (produceCacheSidecarOnce K.result.load cache).result.next
    let L := installResidentBank N
    let owners := carriedRosterAtEmission X p w Y u K cache keys
    let done := resume ⟨L.result,afterOne B N.birth.job,rfl,owners,labels⟩
    let out := nextR66OwnerScope X p w Y u K cache keys retire labels resume bad B
    out.result=(done.result.1,B) ∧
      out.steps=done.steps+cachedScopeOwn M retire initial (.step p w) u+
        keptSuccessorOwnerScan X p w Y A H := by
  let K := retainActualSelectedDemand X p w Y A M u H
  let made := produceCacheSidecarOnce K.result.load cache
  let N := made.result.next
  let J := N.birth.job
  let L := installResidentBank N
  let owners := carriedRosterAtEmission X p w Y u K cache keys
  let done := resume ⟨L.result,afterOne B J,rfl,owners,labels⟩
  have actual : N=sourceState M (.step p w) u :=
    selected_load_emits_the_actual_driver_source_after_retention X p w Y A M u H cache here
  have newJob : J=(borns M (.step p w) u).job := by
    change N.birth.job=_
    rw [actual]
    rfl
  have ready : JobsReady B [J] := by
    rw [onBank,newJob]
    exact legal (.step p w) u
  have eq := next_R66_scope_keeps_the_paid_roster_and_actual_installed_resident
    X p w Y u K cache keys retire labels resume bad B ready
  have side : made.steps+L.steps=(M.demand Y u).result.sidecarCharge :=
    same_emitted_sidecar_and_install_form_the_actual_load_charge X p w Y u K.result.load cache
  have acq : K.steps=(M.demand Y u).steps+keptSuccessorOwnerScan X p w Y A H := rfl
  have scopeFee :
      cachedScopeOwn M retire initial (.step p w) u =
        ((M.demand Y u).steps+(M.demand Y u).result.sidecarCharge)+
          (publishFee B J.entry J.offset J.built+retire J+4) := by
    unfold cachedScopeOwn
    dsimp only [installedAddonDebit,paidAcquisition]
    rw [←here,←newJob,←onBank]
  change (nextR66OwnerScope X p w Y u K cache keys retire labels resume bad B).result=(done.result.1,B)
    ∧ (nextR66OwnerScope X p w Y u K cache keys retire labels resume bad B).steps=
      done.steps+cachedScopeOwn M retire initial (.step p w) u+keptSuccessorOwnerScan X p w Y A H
  refine ⟨congrArg Meter.result eq,?_⟩
  have steps : (nextR66OwnerScope X p w Y u K cache keys retire labels resume bad B).steps =
      K.steps+(made.steps+L.steps)+(publishFee B J.entry J.offset J.built+done.steps+retire J+4) :=
    congrArg Meter.steps eq
  rw [steps,acq,side,scopeFee]
  omega

#print axioms actual_kept_child_scope_preserves_parent_and_pays_one_owner_scan
end
end J6R114RetainedScopeTariff
