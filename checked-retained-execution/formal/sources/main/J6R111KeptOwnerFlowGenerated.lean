import J6R111KeptOwnerFlowNext
import J6R111KeptOwnerFlowCode
import J6R111KeptOwnerFlowLayout
import J6R94HeldOwnerProviderRosterLayout

/-! Assemble the successor from the complete roster actually received
by the current continuation; derive the outgoing roster and its order
instead of asking for the next kept page as a future oracle answer. -/
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
set_option maxHeartbeats 36000000
set_option maxRecDepth 5800
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)

def scanActualParentOwnerGroups : Meter (ParentOwnerHeaders Y.site) :=
  let R := A.labelled
  groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) A.owners R.input R.ingress R.units
    R.raw.rawView R.axis R.law

theorem the_actual_parent_group_scan_keeps_all_incumbent_owners :
    let H := scanActualParentOwnerGroups X p w Y A
    H.result.order=A.owners.order ∧ ∀ x,x∈H.result.order :=
  ⟨(same_raw_roster_and_actual_labels_supply_true_group_headers Y (gateHistory T (bootGates X) p)
    A.owners A.labelled.input A.labelled.ingress A.labelled.units A.labelled.raw.rawView
      A.labelled.axis A.labelled.law).1,(scanActualParentOwnerGroups X p w Y A).result.all⟩

variable (u : (Plan sel).Slot (p.ticket w).child)
variable (cache : CachedParentFrames Y.site) (port : PaidPortIndex Y)
variable {rank : ℕ} {U : ExplicitSelectedWords Y.site u rank}
variable (R : Replayed Y.site u rank U)
variable (H : ParentOwnerHeaders Y.site)
variable (fallback : Addon (1+(Y.site.ownerWidth+(pageKeyWidth m+pad))) (dim (successorTicket (p.ticket w) u))
  key prec (pageKeyWidth m+pad))
variable (plane : Meter (LoadedPlane Y R))
variable (fitDepth : (p.ticket w).child.depth+1<2^Y.input.dep)
variable (fitPrec : (successorTicket (p.ticket w) u).child.prec<2^prec)
variable {raw : List (Word (rank+1))}
variable (dispatch : Meter (RawFields R raw))

/-- The per-address inputs are the actual physical replay, queries and
dispatch; the complete successor roster is generated here from the
received old roster, not supplied alongside them. The parent can share
`H` across requests (its actual scan is a separate charged operation). -/
def generatedLoadWithOwners :
    Meter (HeldOwnerLoad Y (u:=u) (gateHistory T (bootGates X) p)) :=
  let before := keepR58OwnerLoad Y (gateHistory T (bootGates X) p) cache port R A.owners H
    A.labelled.names fallback plane fitDepth fitPrec dispatch
  retainedWithMeasuredCode Y (gateHistory T (bootGates X) p) before

theorem generated_load_has_the_true_creation_owner_context :
    let K := generatedLoadWithOwners X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
    NativeCreationOwnerContext Y K.result.load :=
  retained_native_code_does_not_change_the_owner_key_context Y (gateHistory T (bootGates X) p) _
    (actual_keepR58_sends_its_own_owner_names Y (gateHistory T (bootGates X) p) cache port
      R A.owners H A.labelled.names fallback plane fitDepth fitPrec dispatch)

theorem generated_code_and_roster_use_one_R58_load_and_one_R102_scan :
    let before := keepR58OwnerLoad Y (gateHistory T (bootGates X) p) cache port R A.owners H
      A.labelled.names fallback plane fitDepth fitPrec dispatch
    let K := generatedLoadWithOwners X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
    (⟨K.result.load,K.steps⟩ : Meter (LocalLoad Y u))=
      (sourceLocalLoad Y cache port R (gateHistory T (bootGates X) p) A.owners H
        A.labelled.names fallback plane fitDepth fitPrec dispatch).bind J6R102NativeCodeMeter.measureLocalLoad ∧
      K.result.held=before.result.held := ⟨rfl,rfl⟩

local instance currentEdge : Fintype (p.ticket w).child.host.Edge := (p.ticket w).child.host.finiteEdge
local instance currentRow : Fintype (p.ticket w).child.host.Row := (p.ticket w).child.host.finiteRow
local instance currentCol : Fintype (p.ticket w).child.host.Col := (p.ticket w).child.host.finiteCol
variable {width : ℕ} (fit : (p.ticket w).child.edges<2^width)

theorem generated_successor_roster_follows_the_literal_layout_ingress_order :
    let K := generatedLoadWithOwners X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
    let keys := generated_load_has_the_true_creation_owner_context X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
    let kept := carriedRosterAtEmission X p w Y u K cache keys
    kept.order=(nativeFull64 Y.site H Y.canonical fit A.labelled.names).order := by
  let K := generatedLoadWithOwners X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
  let keys := generated_load_has_the_true_creation_owner_context X p w Y A u cache port R H fallback plane fitDepth fitPrec dispatch
  have exactOrder := (emitted_child_keeps_the_complete_original_roster_in_its_paid_order X p w Y u K cache keys).1
  change (carriedRosterAtEmission X p w Y u K cache keys).order=
    (openCurrentOwners Y (gateHistory T (bootGates X) p) A.owners H A.labelled.names).result.order at exactOrder
  exact exactOrder.trans (real_next_layout_and_retained_roster_have_identical_order Y
    (gateHistory T (bootGates X) p) A.owners H A.labelled.names fit).symm

#print axioms the_actual_parent_group_scan_keeps_all_incumbent_owners
#print axioms generated_load_has_the_true_creation_owner_context
#print axioms generated_code_and_roster_use_one_R58_load_and_one_R102_scan
#print axioms generated_successor_roster_follows_the_literal_layout_ingress_order
end
end J6R111KeptOwnerFlow

