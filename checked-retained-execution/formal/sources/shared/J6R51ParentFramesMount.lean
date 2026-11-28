import J6R51ParentFramesCache

/-! An explicit paid continuation for the chosen parent: build the
frame cache once, then thread the returned rows, not another writer. -/
namespace J6R51ParentFrames
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage
open J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 13000000
set_option linter.unusedSectionVars false
set_option Elab.async false

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)

def buildSharedCache (bank : AddonRows S) (bankEQ : bank=S.bank)
    (selected : List (PortRow Q.port)) (selectedEQ : selected=S.write.result.selected) :
    Meter (Option (CachedParentFrames S)) :=
  certifyCache S (framesFromSelected S bank selected)
    (shared_parent_frames_exact S bank bankEQ selected selectedEQ).1

def useMountedCache {R : Type} (start : Meter (Option (CachedParentFrames S)))
    (go : CachedParentFrames S→Meter R) (fallback : Unit→Meter R) : Meter R :=
  match start.result with
  | none =>
    let other := fallback ()
    ⟨other.result,start.steps+other.steps+2⟩
  | some cache =>
    let done := go cache
    ⟨done.result,start.steps+done.steps+2⟩

theorem use_mounted_cache_exact {R : Type} (start : Meter (Option (CachedParentFrames S)))
    (go : CachedParentFrames S→Meter R) (fallback : Unit→Meter R)
    (cache : CachedParentFrames S) (h : start.result=some cache) :
    useMountedCache S start go fallback=⟨(go cache).result,start.steps+(go cache).steps+2⟩ := by
  unfold useMountedCache
  rw [h]

theorem mounted_shared_parent_exact_once {R : Type}
    (bank : AddonRows S) (bankEQ : bank=S.bank)
    (selected : List (PortRow Q.port)) (selectedEQ : selected=S.write.result.selected)
    (go : CachedParentFrames S→Meter R) (fallback : Unit→Meter R) :
    let made := buildSharedCache S bank bankEQ selected selectedEQ
    ∃ cache : CachedParentFrames S,
      made.result=some cache ∧ cache.rows=(halfOrder T v Q.native.physical).map S.frame ∧
      useMountedCache S made go fallback=⟨(go cache).result,
        (framesFromSelected S bank selected).steps+3+(go cache).steps+2⟩ := by
  obtain ⟨cache,h,hstep,horder⟩ := certify_cache_success S (framesFromSelected S bank selected)
    (shared_parent_frames_exact S bank bankEQ selected selectedEQ).1
  have result : (buildSharedCache S bank bankEQ selected selectedEQ).result=some cache := h
  have price : (buildSharedCache S bank bankEQ selected selectedEQ).steps=
      (framesFromSelected S bank selected).steps+3 := hstep
  refine ⟨cache,result,horder,?_⟩
  rw [use_mounted_cache_exact S _ go fallback cache result,price]

theorem mounted_rescanned_parent_exact_once {R : Type}
    (bank : AddonRows S) (bankEQ : bank=S.bank) (go : CachedParentFrames S→Meter R)
    (fallback : Unit→Meter R) :
    let made := buildCache S bank bankEQ
    ∃ cache : CachedParentFrames S,
      made.result=some cache ∧ cache.rows=(halfOrder T v Q.native.physical).map S.frame ∧
      useMountedCache S made go fallback=⟨(go cache).result,
        (paidParentFrames S bank).steps+3+(go cache).steps+2⟩ := by
  obtain ⟨cache,h,hstep,horder⟩ := built_cache_is_paid_actual_parent S bank bankEQ
  refine ⟨cache,h,horder,?_⟩
  rw [use_mounted_cache_exact S _ go fallback cache h,hstep]

#print axioms use_mounted_cache_exact
#print axioms mounted_shared_parent_exact_once
#print axioms mounted_rescanned_parent_exact_once
end J6R51ParentFrames
