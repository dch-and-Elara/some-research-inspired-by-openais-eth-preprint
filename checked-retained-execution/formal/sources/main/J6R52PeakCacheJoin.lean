import J6R52PeakCache
import J6R51PeakOnlineBodies
import J6R52CacheSourceActiveMount

/-! The measured cache at a selected real nonroot online call.
This counts an extra cache in that call, not in already suspended
ancestors. The source callback still reads the same child and restores
its expected registry. The all-depth online runner is not redefined. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R49DFS J6R50SourceProducer J6R51Online J6R51Peak J6R51ParentFrames J6R52CacheSource
open J6R48RawRoute J6R36ChildFramedRoute

set_option autoImplicit false
set_option maxRecDepth 3400
set_option maxHeartbeats 15000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem actual_online_nonroot_cache_selected (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (u : (P).Slot c)
    (a : (S).cutoff<((P).child c u).edges) (seed : ℕ)
    (boot : ∀ (w : (P).Slot r) h,
      ((M.initial w).result.birth.native.physical.record h).body.length≤seed) :
    let X := sourceState M p u
    let B := stackBank (borns M) initial (.step p u)
    let body := sourceBodyCap s C seed
    ∃ cache : CachedParentFrames X.site,
      (buildCache X.site X.site.bank rfl).result=some cache ∧
      mountActualActiveParent M retire p u X a B X.site.bank rfl=
        ⟨(runAfter M retire c p u X B).result.1,
          (paidParentFrames X.site X.site.bank).steps+3+(runAfter M retire c p u X B).steps+2⟩ ∧
      cachedAfterRead M retire p u X a B cache=readAfter M retire p u X a B ∧
      (cachedWireBits cache).length≤
        (p.ticket u).child.edges*cachedRowCap X.birth.port X.site.ownerWidth key prec page (dim (p.ticket u)) body := by
  dsimp only
  let X := sourceState M p u
  let B := stackBank (borns M) initial (.step p u)
  obtain ⟨cache,built,fee⟩ :=
    same_active_occurrence_mounts_frames_once M retire p u X a B X.site.bank rfl
  exact ⟨cache,built,fee,cached_after_read_exact M retire p u X a B cache,
    actual_cached_parent_payload_size cache _ (actual_demanded_body_fits M seed boot p u)⟩

#print axioms actual_online_nonroot_cache_selected
end
end J6R52Peak
