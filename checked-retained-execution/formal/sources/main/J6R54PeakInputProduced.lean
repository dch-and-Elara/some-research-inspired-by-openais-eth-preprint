import J6R54PeakInputEmit
import J6R54PeakInputShare

/-! Observe the real emitter at a chosen cut of the actual compiled
physical parent order for a cached deep demand. The copied heads
become the source's stored input, rather than a separate second
semantic observer standing in for a paid row source. -/
namespace J6R54PeakInput
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J1PPrinted J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33GeneratedChildSite J6R34RootAtlas J6R48DFS J6R48RawRoute J6R48GeneratedAddons
open J6R49SourceLayout J6R50SourceProducer J6R51ParentFrames J6R51Online J6R51Peak
open J6R52CacheSource J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3850
set_option maxHeartbeats 21500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child}

theorem true_cached_emission_does_not_change_the_actual_next_site
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    (produceCacheSidecarOnce K cache).result.next=K.advance.next :=
  congrArg Advance.next (cached_advance_exact X u K cache)

theorem exact_raw_phase_of_actual_cached_descendant
    (K : LocalLoad X u) (cache : CachedParentFrames X.site)
    (before after : List (Port v.child.host.Edge))
    (split : (cachedAdvance X u K cache).next.birth.native.physical.order=before++after) :
    let next := (cachedAdvance X u K cache).next
    let read := K.directory.read X K.event
    let made := emit read next.birth.native.physical.order
    let buffered := before.map (readAndCopyRawHead read)
    let current := next.site.input.take before.length
    made=resumeSiblingRawHeads buffered (emit read after) ∧
      (produceCacheSidecarOnce K cache).steps=made.steps ∧
      next.site.input=made.result ∧
      current=buffered.map Meter.result ∧
      (current.flatMap addonWords).length≤
        before.length*addonCap K.directory.ow (dim (successorTicket v u)) key prec page := by
  let next := (cachedAdvance X u K cache).next
  let read := K.directory.read X K.event
  have kept : next.site.input=(emit read next.birth.native.physical.order).result := rfl
  have paid : (produceCacheSidecarOnce K cache).steps=(emit read next.birth.native.physical.order).steps := rfl
  have actualOrder : next.birth.native.physical.order=before++after := split
  refine ⟨?_,paid,kept,?_,?_⟩
  · rw [actualOrder]
    exact actual_emit_resumes_from_its_copied_heads read before after
  · rw [kept,actualOrder,List.map_map]
    exact named_saved_heads_are_the_same_emitted_prefix read before after
  · rw [kept,actualOrder]
    exact selected_emitter_prefix_bits_fit read before after

#print axioms true_cached_emission_does_not_change_the_actual_next_site
#print axioms exact_raw_phase_of_actual_cached_descendant
end
end J6R54PeakInput
