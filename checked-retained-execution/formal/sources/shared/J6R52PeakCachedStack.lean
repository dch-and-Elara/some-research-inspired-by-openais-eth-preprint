import J6R52PeakCache
import J6R51PeakOnlineDirectory
import J6R52CacheWholeRun

/-! Additional selected frame-cache bits in the actual all-depth
cache-aware runner. Each active loaded site mounts the exact returned
bank, retaining that cache up to the current resumed child. The bound
counts the logical bytes of those mounts only, not allocator metadata
nor the independently resident addon banks. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R49DFS J6R50SourceProducer J6R51Online J6R51Peak J6R51ParentFrames
open J6R16ModeCost J6R48RawRoute J6R36ChildFramedRoute J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 16000000
set_option maxSynthPendingDepth 12
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

def sourceMounted {M : OnlineMachine T key prec tw bw page q}
    (p : Path sel r c) (w : (P).Slot c) :
    Meter (CachedParentFrames (sourceState M p w).site) :=
  let X := sourceState M p w
  mountResident X (installResidentBank X).result

def actualMountedFields (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c) : ℕ :=
  if (S).cutoff<((P).child c w).edges then
    (cachedWireBits (sourceMounted (M:=M) p w).result).length
  else 0

def cacheStackBits (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step p w => cacheStackBits M p + actualMountedFields M p w

def OwnerWidth (M : OnlineMachine T key prec tw bw page q) (owner : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    (sourceState M p w).site.ownerWidth≤owner

theorem actual_active_mount_has_exact_typed_rows_and_fee
    (M : OnlineMachine T key prec tw bw page q)
    (p : Path sel r c) (w : (P).Slot c) :
    let X := sourceState M p w
    let B := (installResidentBank X).result
    let mounted := sourceMounted (M:=M) p w
    mounted.steps=(paidParentFrames X.site B.rows).steps+3+2 ∧
    mounted.result.rows=(childOrder X.site).map (frameOf X.site) ∧
    mounted.result.rows.length=(p.ticket w).child.edges := by
  let X := sourceState M p w
  let B := (installResidentBank X).result
  exact ⟨mounted_resident_fee X B,mounted_resident_uses_real_rows X B,
    (actual_cached_rows_are_the_physical_child (sourceMounted (M:=M) p w).result).2⟩

theorem source_selected_cache_row_width
    (M : OnlineMachine T key prec tw bw page q)
    (fixed addr seed owner : ℕ) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (ownerFits : OwnerWidth M owner)
    (p : Path sel r c) (w : (P).Slot c) :
    actualMountedFields M p w≤((P).child c w).edges *
      cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
  let X := sourceState M p w
  unfold actualMountedFields
  split
  · have bits := actual_cached_parent_payload_size (sourceMounted (M:=M) p w).result _
      (actual_demanded_body_fits M seed boot p w)
    have a : X.birth.port≤addr := by
      have h := (sizes p w).2
      change X.birth.port+6≤addr at h
      omega
    have o : X.site.ownerWidth≤owner := ownerFits p w
    have d : dim (p.ticket w)≤Nat.clog 2 s := bits_le_lam _ _
    have row : cachedRowCap X.birth.port X.site.ownerWidth key prec page (dim (p.ticket w))
          (sourceBodyCap s C seed)≤
        cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
      unfold cachedRowCap
      omega
    exact bits.trans (Nat.mul_le_mul_left _ row)
  · exact Nat.zero_le _

theorem actual_cached_path_frame_bytes
    (M : OnlineMachine T key prec tw bw page q)
    (fixed addr seed owner : ℕ) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (ownerFits : OwnerWidth M owner)
    (p : Path sel r c) :
    cacheStackBits M p≤(3*r.edges/29)*
      cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) := by
  let A := cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed)
  have h : cacheStackBits M p≤spawnedEdgeSum p*A := by
    induction p with
    | root => simp [cacheStackBits,spawnedEdgeSum]
    | step p w ih =>
      simp only [cacheStackBits,spawnedEdgeSum,Nat.add_mul]
      exact Nat.add_le_add ih (source_selected_cache_row_width M fixed addr seed owner sizes boot ownerFits p w)
  exact h.trans (Nat.mul_le_mul_right _ (spawned_edges_geometric p))

#print axioms actual_active_mount_has_exact_typed_rows_and_fee
#print axioms source_selected_cache_row_width
#print axioms actual_cached_path_frame_bytes
end
end J6R52Peak
