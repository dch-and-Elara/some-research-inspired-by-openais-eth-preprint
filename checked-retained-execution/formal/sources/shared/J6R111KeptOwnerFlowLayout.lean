import J6R111KeptOwnerFlowEntry
import J6R68ActiveInputsBind
import J6R94HeldOwnerProviderRetainLayout

/-! The actual paid parent setup returns both its old active receipt and
the complete labels. The continuation view borrows the emitted labels;
no layout is reproduced at its positive children. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS P11FullPacking
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R68.RecursivePeak
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute
open J6R68ActiveInputs J6R14LayoutCost J6R17ModeTape V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
set_option maxRecDepth 5700
set_option Elab.async false

noncomputable section
section RetainedLayout
variable {f : ℤ[X]} {ell s : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {width : ℕ}
local instance graphEdge : Fintype c.host.Edge := c.host.finiteEdge

def movePacked {a copies w i j : ℕ} (e : i=j) (L : Meter (KeptLayoutWords a copies w i)) :
    Meter (KeptLayoutWords a copies w j) := e ▸ L

theorem movePacked_exact_result {a copies w i j : ℕ} (e : i=j) (L : Meter (KeptLayoutWords a copies w i)) :
    ((movePacked e L).result.receipt=(transportLayout e ⟨L.result.receipt,L.steps⟩).result) ∧
      (movePacked e L).result.labels=L.result.labels ∧ (movePacked e L).steps=L.steps := by
  cases e
  exact ⟨rfl,rfl,rfl⟩

theorem layout_transport_only_casts_result {a copies w i j : ℕ}
    (e : i=j) (L : LayoutReceipt a copies w i) (h k : ℕ) :
    (transportLayout e ⟨L,h⟩).result=(transportLayout e ⟨L,k⟩).result := by
  cases e
  rfl

/-- Execute one selected layout (the very one of ChosenSetup.run), but
do not project away its owner labels. The four control steps are the
original R94 retention fee. -/
def selectedLayoutAndLabels (W : ChosenSetup (c:=c) sel d width) :
    Meter (KeptLayoutWords ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
      (packing sel d).copies (width+1) c.edges) :=
  let count := layout_actual_edge_count (s:=s) (c:=c) d
  let fit := Eq.mpr (congrArg (fun e : ℕ=>e<2^width) count) W.fit
  movePacked count (paidSelectedSetupRetainingCompleteLabels W.input (packing sel d) width W.pos W.dim
    fit W.coordinate W.exactLabels W.rounding W.bytes)

theorem one_parent_layout_produces_old_bytes_and_all_retained_labels
    (W : ChosenSetup (c:=c) sel d width) :
    let out := selectedLayoutAndLabels W
    out.result.receipt=W.run.result ∧ out.result.labels=(runWithIngress W.input width W.bytes).result.vertexLabels ∧
      out.steps=W.run.steps+4 := by
  let count := layout_actual_edge_count (s:=s) (c:=c) d
  let fit := Eq.mpr (congrArg (fun e : ℕ=>e<2^width) count) W.fit
  let A := paidSelectedSetupRetainingCompleteLabels W.input (packing sel d) width W.pos W.dim
    fit W.coordinate W.exactLabels W.rounding W.bytes
  let O := paidSelectedSetup W.input (packing sel d) width W.pos W.dim
    fit W.coordinate W.exactLabels W.rounding W.bytes
  have capture := movePacked_exact_result count A
  have retained := retained_layout_has_unchanged_projection_and_one_layout_fee W.input
    (packing sel d) width W.pos W.dim fit W.coordinate W.exactLabels W.rounding W.bytes
  change (movePacked count A).result.receipt=(transportLayout count O).result ∧
    (movePacked count A).result.labels=(runWithIngress W.input width W.bytes).result.vertexLabels ∧
    (movePacked count A).steps=(transportLayout count O).steps+4
  refine ⟨?_,capture.2.1.trans retained.2.1,?_⟩
  · rw [capture.1]
    change (transportLayout count ⟨A.result.receipt,A.steps⟩).result=(transportLayout count O).result
    rw [show A.result.receipt=O.result from retained.1]
    change (transportLayout count ⟨O.result,A.steps⟩).result=
      (transportLayout count ⟨O.result,O.steps⟩).result
    exact layout_transport_only_casts_result count O.result A.steps O.steps
  · rw [capture.2.2,transportLayout_steps]
    exact retained.2.2
end RetainedLayout

section Borrow
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant
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
variable (R : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p)))
variable {width : ℕ}
local instance labelEdge : Fintype c.host.Edge := c.host.finiteEdge

variable (W : ChosenSetup (c:=c) sel (ticketReady T (p.ticket w)) width)
variable (actual : KeptLayoutWords ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
  (packing sel (ticketReady T (p.ticket w))).copies (width+1) c.edges)
variable (emitted : actual=(selectedLayoutAndLabels W).result)
variable (names : Function.Injective Y.site.oldKey)
variable (order : R.order=W.input.order)
variable (selected : W.input.run.result.2=W.input.order.map (fun v=>W.input.format.label
  (wordsOf (packing sel (ticketReady T (p.ticket w))) v)))

/-- Build the witness from an already emitted result. `actual`, not a
new call to the layout builder, is its `.raw` payload. The axis is
read from the actual child's own issued word record. -/
def useAlreadyEmittedLabels : LabelWitness X p w Y R :=
  ⟨names,W.input,W.bytes,width,_,_,_,_,actual,Y.input.words.result.axis,
    ⟨order,(congrArg KeptLayoutWords.labels emitted).trans
      (one_parent_layout_produces_old_bytes_and_all_retained_labels W).2.1,
      selected,W.coordinate,rfl⟩⟩

theorem borrowing_the_actual_emitted_result_uses_its_same_bytes :
    let owed := useAlreadyEmittedLabels X p w Y R W actual emitted names order selected
    HEq owed.raw actual ∧ owed.axis=Y.input.words.result.axis := ⟨HEq.rfl,rfl⟩
end Borrow

#print axioms one_parent_layout_produces_old_bytes_and_all_retained_labels
#print axioms borrowing_the_actual_emitted_result_uses_its_same_bytes
end
end J6R111KeptOwnerFlow

