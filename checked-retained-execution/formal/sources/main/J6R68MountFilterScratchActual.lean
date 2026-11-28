import J6R68MountFilterScratchCore
import J6R68RecursivePeakMountScratch

/-! The cut belongs to the actual active R66 mount's one paid
ParentFrames scan. The incoming bank and ancestor caches are the same
as in the subsequent MountScratch theorem. The current cache is not
yet allocated as a completed output at this first phase. -/
namespace J6R68.MountFilterScratch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R51ParentFrames J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS J6R36ChildFramedRoute J6R25PreparedSupply
open J6R68.RecursivePeak J6R52CacheSource

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4700
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

theorem actual_mount_consumes_this_single_physical_filter
    (M : Machine) (B : L) (p : Path sel r c) (w : (P).Slot c) (j : ℕ) :
    let E := sourceEntered M B p w
    let selected := observeSelection E.site.birth.native.gWord j E.site.birth.native.physical.raw
    let framed := framesFromSelected E.site.site E.resident.rows selected.1.result
    paidParentFrames E.site.site E.resident.rows=
      ⟨framed.result,selected.1.steps+framed.steps+5⟩ ∧
      (mountResident E.site E.resident).steps=selected.1.steps+framed.steps+10 := by
  let E := sourceEntered M B p w
  let selected := observeSelection E.site.birth.native.gWord j E.site.birth.native.physical.raw
  let framed := framesFromSelected E.site.site E.resident.rows selected.1.result
  have proj : selected.1=selectPorts E.site.birth.native.gWord E.site.birth.native.physical.raw :=
    observed_projection_is_the_literal_selector _ _ _
  have exactParent :
      paidParentFrames E.site.site E.resident.rows=⟨framed.result,selected.1.steps+framed.steps+5⟩ := by
    change paidParentFrames E.site.site E.resident.rows=
      ⟨(framesFromSelected E.site.site E.resident.rows selected.1.result).result,
       selected.1.steps+(framesFromSelected E.site.site E.resident.rows selected.1.result).steps+5⟩
    rw [proj]
    rfl
  refine ⟨exactParent,?_⟩
  obtain ⟨_,_,paid,_⟩ :=
    built_cache_is_paid_actual_parent E.site.site E.resident.rows E.resident.exactRows
  change (mountResident E.site E.resident).steps=selected.1.steps+framed.steps+10
  change (buildCache E.site.site E.resident.rows E.resident.exactRows).steps+2=_
  rw [paid,exactParent]

theorem actual_filter_cut_is_bounded_without_any_current_completed_frame_cache
    (shared paused : ℕ) (M : Machine) (B : L)
    (p : Path sel r c) (w : (P).Slot c) (j : ℕ) :
    let E := sourceEntered M B p w
    let cut := (observeSelection E.site.birth.native.gWord j E.site.birth.native.physical.raw).2
    unmountedChildResidentBits shared paused M B p w+cut.namedPayloadBits physicalPortWords ≤
      unmountedChildResidentBits shared paused M B p w+(sourcePhysicalBitTape E.site.input).length := by
  let E := sourceEntered M B p w
  let raw := E.site.birth.native.physical.raw
  have code (x : PortRow E.site.birth.port) :
      x.body.length+1 ≤ (physicalPortWords x).length := by
    rw [physical_port_words_exact]
    omega
  have fit := pending_copies_and_selected_suffix_fit_the_disjoint_source E.site.birth.native.gWord
    j raw physicalPortWords code
  have same := compiled_occurrence_uses_same_physical_port_tape E.site.input
  change raw.flatMap physicalPortWords=sourcePhysicalBitTape E.site.input at same
  rw [same] at fit
  exact Nat.add_le_add_left fit _

theorem actual_filter_cut_has_the_same_parent_extent_bound
    (shared paused : ℕ) {cw ew : ℕ}
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (fixed addr seed : ℕ) (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (p : Path sel r c) (w : (P).Slot c) (j : ℕ) :
    let entered := sourceEntered M B p w
    let cut := (observeSelection entered.site.birth.native.gWord j entered.site.birth.native.physical.raw).2
    unmountedChildResidentBits shared paused M B p w+cut.namedPayloadBits physicalPortWords ≤
      unmountedChildResidentBits shared paused M B p w+(2*c.edges)*(addr+sourceBodyCap s C seed) := by
  have actual := actual_filter_cut_is_bounded_without_any_current_completed_frame_cache
    shared paused M B p w j
  have room := actual_demanded_occurrence_port_bits_uniform (shadow M F E B own) fixed addr seed sizes boot p w
  rw [shadow_stored_sites_unchanged] at room
  exact actual.trans (Nat.add_le_add_left room _)

#print axioms actual_mount_consumes_this_single_physical_filter
#print axioms actual_filter_cut_is_bounded_without_any_current_completed_frame_cache
#print axioms actual_filter_cut_has_the_same_parent_extent_bound
end
end J6R68.MountFilterScratch
