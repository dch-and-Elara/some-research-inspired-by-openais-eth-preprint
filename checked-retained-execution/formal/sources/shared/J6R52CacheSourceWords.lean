import J6R52CacheSourceReplay

/-! The mounted replay tariff occupies the existing physical slot, so
a later actual publication pays it once rather than adding a second
copy to the outer descriptor acquisition. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R34RootAtlas J6R10Repack

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

theorem transported_modes {E A B : Type} {N : Network E A B} {a q p : ℕ}
    {P : PhysicalPacking N a (Fin 64)} {i : Fin a} {x y : ChildResidents a q}
    (H : ResidentReceipt P i p x) (h : x=y) :
    (h ▸ H : ResidentReceipt P i p y).modes=H.modes := by
  cases h
  rfl

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

def meterPhysical (W : OccurrenceWordsOnly T ticket key prec tw bw page)
    (M : Meter (ChildResidents ((SP).levelBits ticket.parent.depth) W.q))
    (same : M.result=W.physical.result) :
    OccurrenceWordsOnly T ticket key prec tw bw page :=
  let H : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision SP ticket.parent ticket.centerAt) M.result := same.symm ▸ W.geometry
  have modeEq : H.modes=W.geometry.modes := transported_modes W.geometry same.symm
  { W with
    physical := M
    geometry := H
    codeFit := by rw [modeEq]; exact W.codeFit
    acted := by rw [modeEq]; exact W.acted }

theorem meter_physical_uses_read (W : OccurrenceWordsOnly T ticket key prec tw bw page)
    (M : Meter (ChildResidents ((SP).levelBits ticket.parent.depth) W.q))
    (same : M.result=W.physical.result) :
    (meterPhysical W M same).physical=M := rfl

theorem meter_physical_identity (W : OccurrenceWordsOnly T ticket key prec tw bw page)
    (M : Meter (ChildResidents ((SP).levelBits ticket.parent.depth) W.q))
    (same : M.result=W.physical.result) (paid : M=W.physical) :
    meterPhysical W M same=W := by
  subst M
  cases W
  rfl

def cachedLocalWords (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    OccurrenceWordsOnly T (successorTicket v u) key prec tw bw page :=
  meterPhysical (localEventWords K.event)
    (cachePhysical X.site u K.rankWidth K.selectedWords cache K.replay)
    (congrArg Meter.result (cache_physical_exact X.site u K.rankWidth K.selectedWords cache K.replay))

theorem cached_local_words_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    cachedLocalWords X u K cache=localEventWords K.event :=
  meter_physical_identity _ _ _ (cache_physical_exact X.site u K.rankWidth K.selectedWords cache K.replay)

/-- The old event and directory still specify the exact same local
addresses. The physical component is now obtained by an actual cache
read, not by evaluating the predecessor's old framed producer. -/
def cachedLocalInput (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    OccurrenceInput T (successorTicket v u) key prec tw bw page :=
  (cachedLocalWords X u K cache).bind (selectedAdjacent K.replay).generated

theorem cached_local_input_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    cachedLocalInput X u K cache=localEventInput K.event := by
  unfold cachedLocalInput localEventInput
  rw [cached_local_words_exact]

#print axioms meter_physical_uses_read
#print axioms meter_physical_identity
#print axioms cached_local_words_exact
#print axioms cached_local_input_exact
end
end J6R52CacheSource
