import J6R52CacheSourceActiveRead
import J6R51ParentFramesMount

/-! One actual active occurrence consumes a paid resident bank,
produces one frame cache, and runs the unchanged active evaluator.
The resulting cache is passed to *all* of this occurrence's live
reads. Deeper active occurrences still use the inherited R51 runner. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 10000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)

def mountActualActiveParent
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (bank : AddonRows X.site) (sameBank : bank=X.site.bank) :
    Meter (Block (T.frame (Path.step p u).reached) ell) :=
  useMountedCache X.site (buildCache X.site bank sameBank)
    (fun cache=>cachedActiveAfter M retire p u X a B cache)
    (fun _=>project (runAfter M retire c p u X B))

theorem same_active_occurrence_mounts_frames_once
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges)
    (B : L) (bank : AddonRows X.site) (sameBank : bank=X.site.bank) :
    ∃ cache : CachedParentFrames X.site,
      (buildCache X.site bank sameBank).result=some cache ∧
      mountActualActiveParent M retire p u X a B bank sameBank=
        ⟨(runAfter M retire c p u X B).result.1,
          (paidParentFrames X.site bank).steps+3+(runAfter M retire c p u X B).steps+2⟩ := by
  obtain ⟨cache,read,_,pay⟩ := mounted_rescanned_parent_exact_once X.site bank sameBank
    (fun cache=>cachedActiveAfter M retire p u X a B cache)
    (fun _=>project (runAfter M retire c p u X B))
  refine ⟨cache,read,?_⟩
  unfold mountActualActiveParent
  rw [pay,cached_active_after_is_actual M retire p u X a B cache]
  rfl

#print axioms same_active_occurrence_mounts_frames_once
end
end J6R52CacheSource
