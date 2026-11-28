import J6R111KeptOwnerFlowRunRoot
import J6R94ExteriorDebitCurrent
import J6R94HeldOwnerProviderHeaders

/-! The first retained owner table and the paid exterior layout share
their physical enumeration. Keep the full label result, rather than
reconstructing isolated owner labels from the graph projection. -/
namespace J6R111KeptOwnerFlow
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R27OriginalGate J6R35RootOrigins
open J6Mesh J6OrientedHost J6R34RootAtlas J6R24LegalLayout J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R55TerminalOrigin J6R51Online J6R30ProducedGateRegistry
open J6R12Blueprint J6R11Blueprint J1PPrinted J6ActiveRun J6R24MeteredRecursion
open J6R68ActiveInputs J6R94ExteriorDebit J6R10Repack V8NativeMessage.N2DLabels

open J6R21Ancestor J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R26DescriptorTree
open J6R48DFS J6ActiveSchedule J6R50SourceProducer J6R64Active J6R66Active
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R62ActivePrep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1300000
set_option maxRecDepth 5000
set_option Elab.async false
set_option quotPrecheck false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (head : OwnsHeader X.header.result B)
variable (gate : Stamp key prec)
variable {own : ℕ} {name : SourceVertex P→Word own} (boot : RootRoster (P:=P) gate pad name)
variable (stock : RootLayoutStock P name)

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Pth" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))
local notation "Dim" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
  (exteriorChild G ell X.centre X.sample X.group).depth)

local instance exteriorLabelsEdges : Fintype (exteriorChild G ell X.centre X.sample X.group).host.Edge :=
  (exteriorChild G ell X.centre X.sample X.group).host.finiteEdge

theorem literal_first_mount_keeps_the_complete_source_order
    (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
    (slot : LiteralFirstSlot X gate pad boot w T) (hname : Function.Injective name) :
    (assembleFirstExteriorKeepingOwners X w gate boot slot B live hname).result.owners.order =
      stageOwnerOrder X boot.order := rfl

variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (first : FirstSource X M)
variable (old : CurrentLayoutSources T key prec tw bw (pageKeyWidth m+pad) rank X.header.result)
variable (issued : Word key) (sameWord : issued=X.issue.result)
variable (fits : Fintype.card (exteriorChild G ell X.centre X.sample X.group).host.Edge < 2^rank)
variable (shape : RootOrderMatch (T:=T) X pad stock fits)
variable (inputs : Full64PlanInputs (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

/-- The inputs certificate names the selected physical chart. Merely
knowing that the ordered header rows enumerate the same owners would
not determine the complete output word, especially on isolated owners. -/
def exteriorLabelsOnTheSamePaidIngress
    (bootOrder : ∀ w,(first.make w).result.owners.order=stageOwnerOrder X boot.order)
    (commonRootOrder : stock.order=boot.order)
    (sameInput : ∀ on : (SP).cutoff<(Ext).edges, shape.input=inputs Ext (readyAtPath T Pth on))
    (samePacking : ∀ on : (SP).cutoff<(Ext).edges,
      packing (forget (full64Selector inputs)) (readyAtPath T Pth on)=packing sel (readyAtPath T Pth on)) :
    ExteriorLabels X M first rank where
  setup on := (withActualExteriorLayout X pad stock B live head issued sameWord fits old shape).exterior B head on
  order on w := by
    change (first.make w).result.owners.order=shape.input.order
    (rw [shape.order,bootOrder w,←commonRootOrder]; rfl)
  exactLabels on := by
    change shape.input.run.result.2=shape.input.order.map (fun v=>shape.input.format.label
      (wordsOf (packing sel (readyAtPath T Pth on)) v))
    rw [sameInput on]
    have exactWord := (full64_selected_receipt inputs (readyAtPath T Pth on)).2.2.1
    rw [samePacking on] at exactWord
    exact exactWord

theorem first_exterior_label_setup_uses_the_one_real_existing_debit
    (bootOrder : ∀ w,(first.make w).result.owners.order=stageOwnerOrder X boot.order)
    (commonRootOrder : stock.order=boot.order)
    (sameInput : ∀ on : (SP).cutoff<(Ext).edges, shape.input=inputs Ext (readyAtPath T Pth on))
    (samePacking : ∀ on : (SP).cutoff<(Ext).edges,
      packing (forget (full64Selector inputs)) (readyAtPath T Pth on)=packing sel (readyAtPath T Pth on))
    (on : (SP).cutoff<(Ext).edges) :
    let chosen := exteriorLabelsOnTheSamePaidIngress X B live head gate boot stock M first old
      issued sameWord fits shape inputs bootOrder commonRootOrder sameInput samePacking
    (chosen.setup on).bytes.paid=
      (exteriorIngressFromIssued X pad stock B live head issued sameWord rank Dim fits).paid :=
  actual_received_exterior_layout_uses_the_paid_ingress X pad stock B live head issued sameWord fits old shape on

#print axioms literal_first_mount_keeps_the_complete_source_order
#print axioms exteriorLabelsOnTheSamePaidIngress
#print axioms first_exterior_label_setup_uses_the_one_real_existing_debit

end
end J6R111KeptOwnerFlow