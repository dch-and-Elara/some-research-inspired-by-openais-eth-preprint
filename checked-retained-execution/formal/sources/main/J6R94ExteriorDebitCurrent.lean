import J6R94ExteriorDebitIssued
import J6R94ExteriorDebitCap
import J6R68ActiveInputsBind

/-! The current layout callback receives the *held* exterior operands.
Only this one callback is installed; its native descendants use their
existing actual producer (including any already wired R82/R94 source).
The stored matching setup fixes all metadata and the same ordered
Full64Input. In particular we do not infer a time bound for any other
layout or for an arbitrary prior Meter. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R27OriginalGate J6Mesh J6OrientedHost
open J6R54ExteriorOwner J6R35RootOrigins J6R30GeneratedRootLayout J6R28GeneratedRootFrame
open J6R26StablePreparedRoot J6R10Repack J6R24LegalLayout J6R26DescriptorTree
open J6R12CollisionGreedyStep J6R68ActiveInputs V8NativeMessage.N2DLabels
open J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R64Active
open J6R32StatefulArithmetic J6ActiveRun J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion J6R50SourceProducer
open J1PPrinted J6R10Reachable J6R51Online P11FullPacking J6R12CollisionMenu J6R14LayoutCost J6R17ModeTape J6R62ActivePrep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section

/-- Retype only the two specification equalities, keep the executable
Meter field as-is. No field comparison or input rewriting is run. -/
def sameFormatIngress {E R C : Type*} [Fintype E] {a : ℕ} {N : Network E R C}
    {I J : Full64Input N a} (h : I=J) (u : Ingress I) : Ingress J :=
  ⟨u.paid,by rw [←h]; exact u.commands,by rw [←h]; exact u.incidences⟩

variable {V : Type} [Fintype V] {m n base native : ℕ} {P : Plant V m n}
variable {f : ℤ[X]}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw) (pad : ℕ)
variable {name : SourceVertex P→Word own} (S0 : RootLayoutStock P name)
variable (buf : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) buf) (head : OwnsHeader X.header.result buf)
variable (issued : Word key) (sameWord : issued=X.issue.result)
variable {s C rank rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}

local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "DIM" => (J6ActiveRun.Shape.levelBits SP (J6ActiveRun.Call.depth Ext))
local instance inletExtEdge : Fintype (Ext).host.Edge := (Ext).host.finiteEdge
local instance inletExtRow : Fintype (Ext).host.Row := (Ext).host.finiteRow
local instance inletExtCol : Fintype (Ext).host.Col := (Ext).host.finiteCol
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "HerePath" => (Path.root : Path sel Ext Ext)

variable (fits : Fintype.card ((exteriorChild G ell X.centre X.sample X.group).host.Edge)<2^rank)

/-- The existing selector/rounding certificate, separated from its
(old and possibly opaque) byte supplier. These are proof fields only. -/
structure RootChoiceLaws (I : CallFormat SP Ext)
    (active : (SP).cutoff<(Ext).edges) : Prop where
  pos : 0<rank
  dim : DIM≤rank
  edgeFit : (Ext).edges<2^rank
  coordinate : ∀ w,I.format.label w=coordinateLabel w
  exactLabels : I.run.result.1=I.format.graph
    (fun v=>some (wordsOf (packing sel (readyAtPath T HerePath active)) v))
  rounding : RoundsExactly (packing sel (readyAtPath T HerePath active))
  measured : I.run.steps≤I.fee

/-- Already held matching layout metadata, without any old byte Meter.
This exact guard covers physical edge order, owner names and declaration
order, Page keys, widths, and label alphabet. -/
structure RootOrderMatch where
  input : CallFormat SP Ext
  order : input=printedExteriorFull64 X pad S0 rank DIM fits
  laws : ∀ active : (SP).cutoff<(Ext).edges,
    RootChoiceLaws (T:=T) (rank:=rank) X input active

variable (source : CurrentLayoutSources T key prec tw bw (pageKeyWidth m+pad) rank X.header.result)
variable (shape : RootOrderMatch (T:=T) X pad S0 fits)

def withActualExteriorLayout : CurrentLayoutSources T key prec tw bw (pageKeyWidth m+pad) rank X.header.result :=
  {source with
    exterior := fun _ _ active =>
      let w := shape.laws active
      let inlet := exteriorIngressFromIssued X pad S0 buf live head issued sameWord rank DIM fits
      ⟨shape.input,sameFormatIngress shape.order.symm inlet,
        w.pos,w.dim,w.edgeFit,w.coordinate,w.exactLabels,w.rounding,w.measured⟩}

theorem selected_exterior_layout_keeps_exact_format
    (active : (SP).cutoff<(Ext).edges) :
    ((withActualExteriorLayout X pad S0 buf live head issued sameWord fits source shape).exterior buf head active).input
      =shape.input := rfl


theorem actual_received_exterior_layout_uses_the_paid_ingress
    (active : (SP).cutoff<(Ext).edges) :
    ((withActualExteriorLayout X pad S0 buf live head issued sameWord fits source shape).exterior buf head active).bytes.paid=
      (exteriorIngressFromIssued X pad S0 buf live head issued sameWord rank DIM fits).paid := rfl

theorem actual_received_exterior_layout_keeps_native_children {c : Call (PhysicalHost f ell)}
    (p : Path sel Ext c) (w : (@Plan f ell s sel).Slot c)
    (site : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
    (active : (SP).cutoff<((@Plan f ell s sel).child c w).edges) :
    (withActualExteriorLayout X pad S0 buf live head issued sameWord fits source shape).after p w site active=
      source.after p w site active := rfl

theorem actual_received_exterior_layout_has_the_checked_debit
    (K : ℕ) (capacity : ExteriorInputWidths X pad S0 buf K)
    (active : (SP).cutoff<(Ext).edges) :
    ((withActualExteriorLayout X pad S0 buf live head issued sameWord fits source shape).exterior buf head active).bytes.paid.steps
      ≤ installedExteriorRawRoof K := by
  let A := (exteriorIngressFromIssued X pad S0 buf live head issued sameWord rank DIM fits).paid
  change A.steps ≤ installedExteriorRawRoof K
  exact same_paid_root_operand_has_derived_rawDebit X pad S0 buf live head rank DIM K fits capacity A
    (actual_issued_word_uses_the_same_checked_ingress X pad S0 buf live head issued sameWord rank DIM fits)

theorem root_and_measured_native_children_supply_the_actual_rawDebit
    (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
    (K nativeCap : ℕ) (capacity : ExteriorInputWidths X pad S0 buf K)
    (native : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel Ext c)
      (w : (@Plan f ell s sel).Slot c) (active : (SP).cutoff<((@Plan f ell s sel).child c w).edges),
      letI := ((@Plan f ell s sel).child c w).host.finiteEdge
      (source.after p w (sourceState M p w) active).bytes.paid.steps ≤ nativeCap)
    {c : Call (PhysicalHost f ell)} (p : Path sel Ext c) (active : (SP).cutoff<c.edges) :
    letI := c.host.finiteEdge
    ((withActualExteriorLayout X pad S0 buf live head issued sameWord fits source shape).atPath M buf head p active).bytes.paid.steps
      ≤ max (installedExteriorRawRoof K) nativeCap := by
  cases p with
  | root =>
    exact (actual_received_exterior_layout_has_the_checked_debit X pad S0 buf live head
      issued sameWord fits source shape K capacity active).trans (le_max_left _ _)
  | step p w =>
    exact (native p w active).trans (le_max_right _ _)


#print axioms sameFormatIngress
#print axioms RootChoiceLaws
#print axioms RootOrderMatch
#print axioms withActualExteriorLayout
#print axioms selected_exterior_layout_keeps_exact_format
#print axioms actual_received_exterior_layout_uses_the_paid_ingress
#print axioms actual_received_exterior_layout_keeps_native_children
#print axioms actual_received_exterior_layout_has_the_checked_debit
#print axioms root_and_measured_native_children_supply_the_actual_rawDebit
end
end J6R94ExteriorDebit

