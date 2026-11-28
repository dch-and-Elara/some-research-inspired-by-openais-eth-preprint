import J6R111KeptOwnerFlowNext
import J6R94HeldOwnerProviderRosterLayout

/-! Legacy selected R108 demand ABI: execute it without changing its
route, and append a separately billed concrete owner scan. This alternative
needs exact agreement of its advertised successor keys with those produced
by the existing old-owner pass. The literal R58 branch instead keeps the
table it already paid to generate. -/
namespace J6R111KeptOwnerFlow
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
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
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

def retainActualSelectedDemand :
    Meter (HeldOwnerLoad Y (u:=u) (gateHistory T (bootGates X) p)) :=
  let request := M.demand Y u
  let ownerRows := openCurrentOwners Y (gateHistory T (bootGates X) p) A.owners H A.labelled.names
  ⟨⟨request.result,ownerRows.result⟩,request.steps+ownerRows.steps⟩

/-- The same real selected demand is not repriced. It is joined with a
separately executed scan of the received complete owner table. -/
theorem same_selected_request_keeps_its_exact_load_and_pays_the_new_complete_pass :
    let prior := M.demand Y u
    let O := openCurrentOwners Y (gateHistory T (bootGates X) p) A.owners H A.labelled.names
    let paid := retainActualSelectedDemand X p w Y A M u H
    paid.result.load=prior.result ∧ paid.result.held=O.result ∧ paid.steps=prior.steps+O.steps :=
  ⟨rfl,rfl,rfl⟩

variable (cache : CachedParentFrames Y.site)

theorem selected_load_emits_the_actual_driver_source_after_retention
    (here : Y=sourceState M p w) :
    (produceCacheSidecarOnce (retainActualSelectedDemand X p w Y A M u H).result.load cache).result.next=
      sourceState M (.step p w) u := by
  apply made_successor_on_the_exact_selected_load_is_the_next_R66_source X p w Y u _ cache M here
  subst Y
  rfl

variable (keys : NativeCreationOwnerContext Y (M.demand Y u).result)
local instance currentEdge : Fintype (p.ticket w).child.host.Edge := (p.ticket w).child.host.finiteEdge
local instance currentRow : Fintype (p.ticket w).child.host.Row := (p.ticket w).child.host.finiteRow
local instance currentCol : Fintype (p.ticket w).child.host.Col := (p.ticket w).child.host.finiteCol

theorem same_selected_demand_retains_exact_complete_native_layout_order
    {width : ℕ} (fit : (p.ticket w).child.edges<2^width) :
    let K := retainActualSelectedDemand X p w Y A M u H
    (carriedRosterAtEmission X p w Y u K cache keys).order=
      (nativeFull64 Y.site H Y.canonical fit A.labelled.names).order := by
  let K := retainActualSelectedDemand X p w Y A M u H
  have same := (emitted_child_keeps_the_complete_original_roster_in_its_paid_order X p w Y u K cache keys).1
  exact same.trans (real_next_layout_and_retained_roster_have_identical_order Y
    (gateHistory T (bootGates X) p) A.owners H A.labelled.names fit).symm

#print axioms same_selected_request_keeps_its_exact_load_and_pays_the_new_complete_pass
#print axioms selected_load_emits_the_actual_driver_source_after_retention
#print axioms same_selected_demand_retains_exact_complete_native_layout_order
end
end J6R111KeptOwnerFlow

