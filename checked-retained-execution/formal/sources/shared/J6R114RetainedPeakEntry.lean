import J6R111KeptOwnerFlowEntry
import J6R52CacheWholePrep
import J6R52PeakCache
import J6R53PeakAddonCore
import J6R66BootPeakMount
import J6R75RawPeakLayoutWords

/-! Named payloads of one actually entered retained invocation. The
fields are observed in their source encodings; computing a flattened
length here does not allocate a flattened copy in the evaluator. -/
namespace J6R114RetainedPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost
open J6Mesh J6R34RootAtlas J6R24LegalLayout J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R34ChildPath J6R54TerminalBoot J6R53OldOwner J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole
open J6R52FreshExterior J6R94HeldOwnerProvider J6R111KeptOwnerFlow
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R66.BootPeak J6R75RawPeak
open J6R68ActiveInputs J6R14LayoutCost V8NativeMessage.N2DLabels J6R51Peak J6R36ChildFramedRoute

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4700
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-- The three actual retained output tapes. The old packed boxes and
copy word remain held along with the newly saved raw labels. -/
def packedKeptBits {a copies w edges : ℕ} (L : KeptLayoutWords a copies w edges) : ℕ :=
  rawLayoutBits rawExportLayoutBits L.receipt.boxes +
    L.receipt.copies.bits.length + selectedLabelBits L.labels

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
local instance retainedSourceEdges : Fintype c.host.Edge := c.host.finiteEdge

-- The live directory is distinct from the installed per-call addon.
-- A later mounted frame cache is a third selected field (below).
def entryKeptBits (shared : ℕ) : ℕ :=
  shared + mountedSelectedBits A.bank + (residentAddonPayload A.resident).length +
    (indexedOwnerTape A.owners.raw).length + packedKeptBits A.labelled.raw +
    A.labelled.axis.length

theorem retained_entry_owner_payload_is_the_full_indexed_file :
    (indexedOwnerTape A.owners.raw).length =
      (ownerTape (A.owners.raw.map RefRow.payload)).length +
        A.owners.raw.length*Y.site.ownerWidth :=
  indexed_owner_tape_adds_address_width A.owners.raw

theorem retained_entry_label_payload_uses_the_complete_owner_order :
    selectedLabelBits A.labelled.raw.labels =
      6*((printedParams (f:=f) (ell:=ell) s).levelBits (p.ticket w).parent.depth)*A.owners.order.length := by
  let H := A.labelled.law
  have same : A.labelled.raw.labels=
      (runWithIngress A.labelled.input A.labelled.units A.labelled.ingress).result.vertexLabels :=
    H.cachedLabels
  rw [same,chosen_greedy_output_preserves_complete_vertex_words,H.selectedLabels,←H.order]
  let enc := fun v : c.host.Row⊕c.host.Col=>
    A.labelled.input.format.label (wordsOf (layout T (p.ticket w)) v)
  have payload : rawLayoutBits List.length (A.owners.order.map enc) =
      (6*((printedParams (f:=f) (ell:=ell) s).levelBits (p.ticket w).parent.depth))*(A.owners.order.map enc).length := by
    apply raw_layout_bits_fixed
    intro k hk
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hk
    change (A.labelled.input.format.label (wordsOf (layout T (p.ticket w)) v)).length=_
    rw [H.serialized,coordinateLabel_len]
  simpa only [List.length_map] using payload

/-- The actual legacy cache is obtained from the very installed
addon object in this entry, rather than from an old prepared run. -/
def heldWithActualParentCache (shared : ℕ) : ℕ :=
  entryKeptBits X p w Y A shared + (cachedWireBits (mountResident Y A.resident).result).length

theorem actual_mount_keeps_the_installed_addon_and_counts_its_frame_cache
    (shared body : ℕ) (fits : ∀ t,(Y.birth.native.physical.record t).body.length≤body) :
    let cache := mountResident Y A.resident
    let installed := (residentAddonPayload A.resident).length
    let full := heldWithActualParentCache X p w Y A shared
    cache.result.rows.length=(p.ticket w).child.edges ∧
    cache.steps=(paidParentFrames Y.site A.resident.rows).steps+3+2 ∧
    installed≤(2*c.edges)*(Y.birth.port+addonCap Y.site.ownerWidth (dim (p.ticket w)) key prec (pageKeyWidth m+pad)) ∧
    full≤entryKeptBits X p w Y A shared+
      (p.ticket w).child.edges*cachedRowCap Y.birth.port Y.site.ownerWidth
        key prec (pageKeyWidth m+pad) (dim (p.ticket w)) body :=
  ⟨(actual_cached_rows_are_the_physical_child (mountResident Y A.resident).result).2,
   mounted_resident_fee Y A.resident, (true_resident_bank_selected_fields A.resident).2,
   Nat.add_le_add_left (actual_cached_parent_payload_size (mountResident Y A.resident).result body fits) _⟩

#print axioms packedKeptBits
#print axioms entryKeptBits
#print axioms retained_entry_owner_payload_is_the_full_indexed_file
#print axioms retained_entry_label_payload_uses_the_complete_owner_order
#print axioms actual_mount_keeps_the_installed_addon_and_counts_its_frame_cache
end
end J6R114RetainedPeak

