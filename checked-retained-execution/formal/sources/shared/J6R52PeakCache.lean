
import J6R51ParentFramesMount
import J6R51PeakSidecar

/-! A real paid parent-cache mount with only selected encoded fields
of the returned frame list charged to storage. Using the cache does
not allocate the flattened observer. The mount and downstream call
are the existing measured primitive, not an arbitrary fee label. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R51Peak J6R51ParentFrames

set_option autoImplicit false
set_option maxRecDepth 3350
set_option maxHeartbeats 13000000

def laneBits {w key prec page : ℕ} (x : Lane w key prec page) : List Bool :=
  x.id.edge.bits++[x.id.col]++originWords x.origin++x.body

def frameBits {w owner key prec page : ℕ} (F : FramedEdge w owner key prec page) : List Bool :=
  F.oldOwner.bits++laneBits F.left++laneBits F.right

def cachedRowCap (w owner key prec page dim body : ℕ) : ℕ :=
  owner+2*(w+key+prec+page+2)+body+dim+3

theorem lane_encoded_bound {w key prec page : ℕ} (x : Lane w key prec page) :
    (laneBits x).length≤w+key+prec+page+2+x.body.length := by
  simp only [laneBits,List.length_append,x.id.edge.size,List.length_cons,List.length_nil,origin_words_exact]
  split <;> omega

theorem true_written_frame_payload_cap {w owner a key prec page : ℕ}
    (keyWord : Word key) (recv : Word prec) (raw : PortRow w)
    (aux : Addon owner a key prec page) (body : ℕ) (fit : raw.body.length≤body) :
    (frameBits (frameView keyWord recv raw aux)).length≤cachedRowCap w owner key prec page a body := by
  let out := frameView keyWord recv raw aux
  have hl := lane_encoded_bound out.left
  have hr := lane_encoded_bound out.right
  have eL : out.left.body.length=raw.body.length+1 := rfl
  have eR : out.right.body.length=a+2 := by
    change (true::aux.parentWasCol::aux.parentSlot.bits).length=_
    simp only [List.length_cons,aux.parentSlot.size]
  rw [eL] at hl
  rw [eR] at hr
  change (frameBits out).length≤_
  simp only [frameBits,List.length_append,out.oldOwner.size,cachedRowCap]
  omega

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {B : Birth T v key prec tw bw page}
variable {old : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}

def cachedWireBits {S : SiteInputs B old} (cache : CachedParentFrames S) : List Bool :=
  cache.rows.flatMap frameBits

theorem actual_cached_rows_are_the_physical_child {S : SiteInputs B old} (cache : CachedParentFrames S) :
    cache.rows=(halfOrder T v B.native.physical).map S.frame ∧ cache.rows.length=v.child.edges := by
  have h : cache.rows=(halfOrder T v B.native.physical).map S.frame :=
    Option.some.inj (cache.exactRows.symm.trans (true_site_issuance S).2.2.2)
  exact ⟨h,by rw [h,List.length_map,half_order_length]⟩

theorem actual_cached_parent_payload_size {S : SiteInputs B old} (cache : CachedParentFrames S)
    (body : ℕ) (fits : ∀ t,(B.native.physical.record t).body.length≤body) :
    (cachedWireBits cache).length≤v.child.edges*cachedRowCap B.port S.ownerWidth key prec page (dim v) body := by
  obtain ⟨same,cnt⟩ := actual_cached_rows_are_the_physical_child cache
  unfold cachedWireBits
  have b := flat_words_bound cache.rows frameBits (cachedRowCap B.port S.ownerWidth key prec page (dim v) body)
    (fun F loc=>by
      rw [same] at loc
      obtain ⟨h,_,e⟩ := List.mem_map.mp loc
      rw [←e]
      exact true_written_frame_payload_cap B.issuance.result B.native.receiving
        (B.native.physical.record h.val) (S.aux h.val) body (fits h.val))
  rw [cnt] at b
  exact b

theorem actual_paid_mount_and_returned_cache_bits (S : SiteInputs B old)
    (bank : AddonRows S) (sameBank : bank=S.bank) {A : Type}
    (child : CachedParentFrames S→Meter A) (fallback : Unit→Meter A)
    (body : ℕ) (fit : ∀ t,(B.native.physical.record t).body.length≤body) :
    let built := buildCache S bank sameBank
    ∃ cache : CachedParentFrames S,
      built.result=some cache ∧
      useMountedCache S built child fallback=
        ⟨(child cache).result,(paidParentFrames S bank).steps+3+(child cache).steps+2⟩ ∧
      (cachedWireBits cache).length≤v.child.edges*cachedRowCap B.port S.ownerWidth key prec page (dim v) body := by
  obtain ⟨cache,built,_,bill⟩ := mounted_rescanned_parent_exact_once S bank sameBank child fallback
  exact ⟨cache,built,bill,actual_cached_parent_payload_size cache body fit⟩

#print axioms lane_encoded_bound
#print axioms true_written_frame_payload_cap
#print axioms actual_cached_rows_are_the_physical_child
#print axioms actual_cached_parent_payload_size
#print axioms actual_paid_mount_and_returned_cache_bits
end J6R52Peak
