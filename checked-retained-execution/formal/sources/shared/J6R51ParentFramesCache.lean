import J6R51ParentFramesCore

/-! Store the paid framing result once. Subsequent selected seat/mode
replays consume only the cached frames; the old framed expression only
appears in the proof-side statement. -/
namespace J6R51ParentFrames
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage
open J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R48RawRoute
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

structure CachedParentFrames where
  rows : FrameRows S
  exactRows : S.write.result.framed=some rows

/-- The result of an earlier paid computation is kept in the cache; its
link to the original parent data is proof-only. -/
def certifyCache (op : Meter (Option (FrameRows S))) (ok : op.result=S.write.result.framed) :
    Meter (Option (CachedParentFrames S)) :=
  match e : op.result with
  | none => ⟨none,op.steps+3⟩
  | some rows => ⟨some ⟨rows,ok.symm.trans e⟩,op.steps+3⟩

theorem certify_cache_success (op : Meter (Option (FrameRows S)))
    (ok : op.result=S.write.result.framed) :
    let result := certifyCache S op ok
    ∃ cache : CachedParentFrames S,
      result.result=some cache ∧ result.steps=op.steps+3 ∧
      cache.rows=(halfOrder T v Q.native.physical).map S.frame := by
  let rows := (halfOrder T v Q.native.physical).map S.frame
  have ref : S.write.result.framed=some rows := (true_site_issuance S).2.2.2
  rcases op with ⟨raw,fee⟩
  change raw=S.write.result.framed at ok
  have made : raw=some rows := ok.trans ref
  cases made
  exact ⟨⟨rows,ref⟩,rfl,rfl,rfl⟩

def buildCache (bank : AddonRows S) (bankEQ : bank=S.bank) : Meter (Option (CachedParentFrames S)) :=
  certifyCache S (paidParentFrames S bank) (paid_parent_frames_exact S bank bankEQ).1

theorem built_cache_is_paid_actual_parent (bank : AddonRows S) (bankEQ : bank=S.bank) :
    let result := buildCache S bank bankEQ
    ∃ cache : CachedParentFrames S,
      result.result=some cache ∧ result.steps=(paidParentFrames S bank).steps+3 ∧
      cache.rows=(halfOrder T v Q.native.physical).map S.frame :=
  certify_cache_success S _ (paid_parent_frames_exact S bank bankEQ).1

variable (u : (Plan sel).Slot v.child) (q : ℕ)

local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits SP v.child.depth)
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))
local notation "i" => (centerIndex d t)

noncomputable def replayCached (U : ExplicitSelectedWords S u q) (cache : CachedParentFrames S) :
    Meter (Option (ChildResidents A q)) :=
  replayWithKeys A q (i).val U.copy U.precision U.masks U.rows (some cache.rows)

theorem replay_cached_is_same_meter (U : ExplicitSelectedWords S u q) (cache : CachedParentFrames S) :
    replayCached S u q U cache=replayChild S u q U := by
  unfold replayCached replayChild
  rw [cache.exactRows]

theorem replay_cached_preserves_receipt (U : ExplicitSelectedWords S u q) (cache : CachedParentFrames S)
    (R : Replayed S u q U) : (replayCached S u q U cache).result=some R.resident :=
  congrArg Meter.result (replay_cached_is_same_meter S u q U cache) |>.trans R.output

#print axioms certify_cache_success
#print axioms built_cache_is_paid_actual_parent
#print axioms replay_cached_is_same_meter
#print axioms replay_cached_preserves_receipt
end J6R51ParentFrames
