import J6R52CacheSourceRoute

/-! The outgoing stored descriptor and its sidecar are built from the
cache-fed physical input at the same actual address. The old input is
only used to prove unchanged typed directory and byte invariants. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R34RootAtlas J6R10Repack J6R48GeneratedAddons
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 10000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def advanceWithInput (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (same : I=localEventInput K.event) : Advance X u :=
  let S := J6R48GeneratedAddons.SiteInputs.fromReader (compileOccurrence I)
    X.childOrigins K.directory.oldKey (J6R49SourceLayout.occurrencePageWord I) (K.directory.read X K.event)
    (fun h=>by
      rw [same]
      exact directory_row_reads_true_origin X K.event K.directory h)
  ⟨⟨I,X.childOrigins,S,rfl⟩,rfl,fun h=>by
    change ((compileOccurrence I).native.physical.record h).body=_
    rw [same]
    exact (true_selected_slot_compilation K.event h).2.1⟩

theorem advance_with_input_eq
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (same : I=localEventInput K.event) : advanceWithInput X u K I same=K.advance := by
  subst I
  rfl

def cachedAdvance (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) : Advance X u :=
  advanceWithInput X u K (cachedRoutedInput X u K cache) (cached_routed_input_exact X u K cache)

theorem cached_advance_uses_real_input
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    (cachedAdvance X u K cache).next.input=cachedRoutedInput X u K cache := rfl

theorem cached_advance_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    cachedAdvance X u K cache=K.advance :=
  advance_with_input_eq X u K _ (cached_routed_input_exact X u K cache)

#print axioms advance_with_input_eq
#print axioms cached_advance_uses_real_input
#print axioms cached_advance_exact
end
end J6R52CacheSource
