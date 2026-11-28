import J6R51ParentFramesCache
import J6R51OnlineCore

/-! A successful paid frame-cache replay is the physical resident
artifact, not an asserted copy of the previous interpreted data. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 6500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

def unwrapSuccess {T : Type} (read : Meter (Option T))
    (has : read.result.isSome) : Meter T :=
  ⟨read.result.get has,read.steps⟩

theorem unwrap_success_exact {T : Type} (read : Meter (Option T))
    (has : read.result.isSome) (result : T) (exactly : read.result=some result) :
    unwrapSuccess read has=⟨result,read.steps⟩ := by
  rcases read with ⟨a,k⟩
  change a=some result at exactly
  cases exactly
  rfl

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {prior : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}

def cachePhysical (S : SiteInputs Q prior) (u : (@Plan f ell s sel).Slot v.child) (q : ℕ)
    (U : ExplicitSelectedWords S u q) (cache : CachedParentFrames S) (H : Replayed S u q U) :
    Meter (ChildResidents ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q) :=
  unwrapSuccess (replayCached S u q U cache) (by
    rw [replay_cached_preserves_receipt S u q U cache H]
    rfl)

theorem cache_physical_exact (S : SiteInputs Q prior) (u : (@Plan f ell s sel).Slot v.child) (q : ℕ)
    (U : ExplicitSelectedWords S u q) (cache : CachedParentFrames S) (H : Replayed S u q U) :
    cachePhysical S u q U cache H=⟨H.resident,(replayChild S u q U).steps⟩ := by
  let op := replayCached S u q U cache
  have h : op.result=some H.resident := replay_cached_preserves_receipt S u q U cache H
  have c : op.steps=(replayChild S u q U).steps :=
    congrArg Meter.steps (replay_cached_is_same_meter S u q U cache)
  unfold cachePhysical
  rw [unwrap_success_exact _ _ _ h,c]

#print axioms unwrap_success_exact
#print axioms cachePhysical
#print axioms cache_physical_exact
end
end J6R52CacheSource
