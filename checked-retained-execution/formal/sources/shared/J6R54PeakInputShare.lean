import J6R52CacheWholeBank
import J6R51PeakGeneratedSidecar

/-! A local refactoring with ONE explicit call of the actual emitter.
The paid result's list is stored in the true new source site. Its fee
is used by the same scoped continuation. Equality of Meter records
with the prior helper does not assert how either definition shares
closures or allocates storage in a compiled runtime. -/
namespace J6R54PeakInput
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J1PPrinted J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33GeneratedChildSite J6R34RootAtlas J6R48DFS J6R48RawRoute J6R48GeneratedAddons
open J6R49SourceLayout J6R50SourceProducer J6R51ParentFrames J6R51Online
open J6R52CacheSource J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3920
set_option maxHeartbeats 23000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def produceStoredInputOnce
    (K : LocalLoad X u) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (exactInput : I=localEventInput K.event) :
    Meter (Advance X u) :=
  let Q := compileOccurrence I
  let pageKey := occurrencePageWord I
  let made := emit (K.directory.read X K.event) Q.native.physical.order
  let S : SiteInputs Q X.childOrigins :=
    ⟨K.directory.ow,K.directory.oldKey,pageKey,made.result,by
      rw [(emit_exact _ _).1]
      exact List.map_congr_left (fun h _=>by
        dsimp only [pageKey]
        rw [exactInput]
        exact directory_row_reads_true_origin X K.event K.directory h)⟩
  let exactAdvance : Advance X u :=
    ⟨⟨I,X.childOrigins,S,rfl⟩,rfl,fun h=>by
      change ((compileOccurrence I).native.physical.record h).body=_
      rw [exactInput]
      exact (true_selected_slot_compilation K.event h).2.1⟩
  ⟨exactAdvance,made.steps⟩

theorem shared_emission_preserves_the_actual_stored_site
    (K : LocalLoad X u) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (exactInput : I=localEventInput K.event) :
    (produceStoredInputOnce K I exactInput).result=advanceWithInput X u K I exactInput := rfl

theorem the_same_emit_output_and_fee_are_used_for_storage
    (K : LocalLoad X u) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (exactInput : I=localEventInput K.event) :
    let Q := compileOccurrence I
    let made := emit (K.directory.read X K.event) Q.native.physical.order
    let out := produceStoredInputOnce K I exactInput
    out.result.next.site.input=made.result ∧ out.steps=made.steps := ⟨rfl,rfl⟩

def produceCacheSidecarOnce (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    Meter (Advance X u) :=
  produceStoredInputOnce K (cachedRoutedInput X u K cache) (cached_routed_input_exact X u K cache)

def openBankDemandSingleEmission {Out : Type}
    (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page)→ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L) : Meter (Out×L) :=
  let made := produceCacheSidecarOnce started.result cache
  let next := made.result.next
  let installed := installResidentBank next
  let out := J6R48DFS.withScope retire next.birth.job (child next installed.result) fallback B
  ⟨out.result,started.steps+(made.steps+installed.steps)+out.steps⟩

theorem single_local_emission_is_exactly_the_original_scoped_meter {Out : Type}
    (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page)→ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L) :
    openBankDemandSingleEmission started cache retire child fallback B=
      openBankDemand started cache retire child fallback B := by
  rfl

#print axioms shared_emission_preserves_the_actual_stored_site
#print axioms the_same_emit_output_and_fee_are_used_for_storage
#print axioms single_local_emission_is_exactly_the_original_scoped_meter
end
end J6R54PeakInput
