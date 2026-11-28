import J6R111KeptOwnerFlowSelected
import J6R57ScopeFeeLedger

/-! The extra owner work of the actual selected demand; no change to the
outgoing load, label tape or existent scope fees. -/
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

def keptSuccessorOwnerScan : ℕ :=
  (openCurrentOwners Y (gateHistory T (bootGates X) p) A.owners H A.labelled.names).steps

theorem actual_selected_demand_charges_the_extra_owner_scan_once :
    let D := M.demand Y u
    let K := retainActualSelectedDemand X p w Y A M u H
    K.result.load=D.result ∧ D.steps+keptSuccessorOwnerScan X p w Y A H=K.steps := by
  exact ⟨rfl,rfl⟩

theorem actual_owner_scan_exact_separate_subcharges :
    let names := actualOwnerNameTape Y H
    let data := bornOwnerData Y (gateHistory T (bootGates X) p) A.owners H
    let ow := 1+(Y.site.ownerWidth+(pageKeyWidth m+pad))
    keptSuccessorOwnerScan X p w Y A H =
      names.steps+data.steps+(3*ow+6)*(bornOwnerOrder Y H).length+15 := by
  unfold keptSuccessorOwnerScan openCurrentOwners unwrapSuccess
  dsimp only
  rw [raw_current_owners_exact Y (gateHistory T (bootGates X) p) A.owners H A.labelled.names]
  dsimp only
  omega

variable (load : LocalLoad Y u) (cache : CachedParentFrames Y.site)

theorem same_emitted_sidecar_and_install_form_the_actual_load_charge :
    let made := produceCacheSidecarOnce load cache
    made.steps+(installResidentBank made.result.next).steps=load.sidecarCharge := by
  let made := produceCacheSidecarOnce load cache
  have paid : made.steps =
      (emit (load.directory.read Y load.event)
        (compileOccurrence (cachedRoutedInput Y u load cache)).native.physical.order).steps :=
    (the_same_emit_output_and_fee_are_used_for_storage load _ (cached_routed_input_exact Y u load cache)).2
  have order : (compileOccurrence (cachedRoutedInput Y u load cache)).native.physical.order =
      load.advance.next.birth.native.physical.order := by
    rw [cached_routed_input_exact]
    rfl
  have next : made.result.next=load.advance.next :=
    one_emission_is_same_actual_next_site load cache
  change made.steps+(installResidentBank made.result.next).steps=load.sidecarCharge
  rw [paid,order,next]
  rfl

#print axioms actual_selected_demand_charges_the_extra_owner_scan_once
#print axioms actual_owner_scan_exact_separate_subcharges
#print axioms same_emitted_sidecar_and_install_form_the_actual_load_charge
end
end J6R114RetainedScopeTariff
