import J6R111KeptOwnerFlowSelected
import J6R111KeptOwnerFlowLayout
import J6R68ActiveInputsSweepEntries

/-! The active call's one kept layout is the source of labels at every
actual successor of this call. Retained owner keys must describe the
same selected source ABI, rather than a reconstructed isomorphic chart. -/
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
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 31500000
set_option maxRecDepth 5500
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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)

local instance hereEdges : Fintype (p.ticket w).child.host.Edge := (p.ticket w).child.host.finiteEdge
local instance hereRows : Fintype (p.ticket w).child.host.Row := (p.ticket w).child.host.finiteRow
local instance hereCols : Fintype (p.ticket w).child.host.Col := (p.ticket w).child.host.finiteCol

/-- The actual current retained operands are scanned once, before a
new layout or any addressed child is produced. -/
def readGroupHeadersForActive : Meter (ParentOwnerHeaders Y.site) :=
  let held := A.labelled
  groupHeadersFromOwnedRaw Y (gateHistory T (bootGates X) p) A.owners held.input held.ingress held.units
    held.raw.rawView held.axis held.law


variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child c w).edges)
variable (H : ParentOwnerHeaders Y.site)

/-- The only additional layout premises beyond the selected producer:
strict physical enumeration order and the receipt for its complete
vertex label words. These are not independent new route data. -/
structure SelectedOwnerLayout (width : ℕ) where
  setup : ChosenSetup (c:=(p.ticket w).child) sel (readyAtPath T (.step p w) on) width
  order : setup.input.order=(nativeFull64 Y.site H Y.canonical setup.fit A.labelled.names).order
  labels : setup.input.run.result.2=setup.input.order.map (fun v=>setup.input.format.label
    (wordsOf (packing sel (readyAtPath T (.step p w) on)) v))

variable (W : SelectedOwnerLayout X p w Y A on H rank)
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (cache : CachedParentFrames Y.site)
variable (keys : NativeCreationOwnerContext Y (M.demand Y u).result)

theorem successor_ticket_uses_the_same_already_selected_Ready :
    ticketReady T ((Path.step p w).ticket u)=readyAtPath T (.step p w) on := rfl

include keys in
theorem carried_successor_names_are_injective :
    let K := retainActualSelectedDemand X p w Y A M u H
    Function.Injective (produceCacheSidecarOnce K.result.load cache).result.next.site.oldKey := by
  let K := retainActualSelectedDemand X p w Y A M u H
  change Function.Injective (produceCacheSidecarOnce K.result.load cache).result.next.site.oldKey
  rw [sidecar_and_cached_scope_produce_the_same_site X p w Y u K cache]
  have context := creation_context_matches_the_real_cached_child Y (gateHistory T (bootGates X) p) K.result cache keys
  change Function.Injective (namesAsRawContext ((cachedAdvance Y u K.result.load cache).next.site.oldKey)).2
  rw [←context]
  exact generated_name_stays_injective Y A.labelled.names

variable (liveWords : KeptLayoutWords
  ((printedParams (f:=f) (ell:=ell) s).levelBits (p.ticket w).child.depth)
  (packing sel (readyAtPath T (.step p w) on)).copies (rank+1) (p.ticket w).child.edges)
variable (kept : liveWords=(selectedLayoutAndLabels W.setup).result)

/-- Reuse the already emitted parent labels, with order and current
owner name injection derived from the actual kept R59-style scan. -/
def checkedChildLabelWords :
    let K := retainActualSelectedDemand X p w Y A M u H
    LabelWitness X (.step p w) u (produceCacheSidecarOnce K.result.load cache).result.next
      (carriedRosterAtEmission X p w Y u K cache keys) := by
  let K := retainActualSelectedDemand X p w Y A M u H
  let next := (produceCacheSidecarOnce K.result.load cache).result.next
  let R := carriedRosterAtEmission X p w Y u K cache keys
  let setup : ChosenSetup (c:=(p.ticket w).child) sel (ticketReady T ((Path.step p w).ticket u)) rank :=
    W.setup
  have order : R.order=setup.input.order :=
    (same_selected_demand_retains_exact_complete_native_layout_order X p w Y A M u H cache keys W.setup.fit).trans W.order.symm
  exact useAlreadyEmittedLabels X (.step p w) u next R setup liveWords kept
    (carried_successor_names_are_injective X p w Y A M H u cache keys) order W.labels

/-- The real R68 active sweep uses its existing numeric code and reads
the actual incoming head once. Its supplied layout is the projection
of the single retained producer, not the old setup rerun for reading. -/
def prepareFromKeptLayout
    (fit : InputFits sel (readyAtPath T (.step p w) on) rate) (chart : MountedChart T)
    (layoutCost : ℕ) :
    Meter (Schedule sel (readyAtPath T (.step p w) on) T.bank rate) :=
  let path := Path.step p w
  let taper := actual_path_taper T path on
  let header := readIncoming Y A.bank A.own
  prepare M.modeWidth fit taper.1 taper.2 X.hf chart.table (chart.covers path on)
    header ⟨liveWords.receipt,layoutCost⟩

#print axioms successor_ticket_uses_the_same_already_selected_Ready
#print axioms carried_successor_names_are_injective
#print axioms checkedChildLabelWords
#print axioms prepareFromKeptLayout
end
end J6R111KeptOwnerFlow

