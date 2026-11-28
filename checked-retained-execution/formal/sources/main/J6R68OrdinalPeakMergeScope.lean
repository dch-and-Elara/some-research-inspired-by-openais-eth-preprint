import J6R68RecursivePeakScope
import J6R63OrdinalDispatchLaws

/-! A current ordinal may replace the exact same checked packet in
the living R66 header scope. Same result is not same acquisition fee.
No assertion here adds a peak from a different execution. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R48RawRoute J6R50SourceProducer J6R51Online J6R51ParentFrames
open J6R52Dispatch J6R52CacheWhole J6R54PeakInput J6R58OrdinalSpace J6R63Ordinal
open J6R64Active J6R66Active J6R66.BootPeak J6R68.RecursivePeak
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4150
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 11000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r} {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
variable {Out : Type}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "nx" => (successorTicket v w)

theorem scope_changes_only_its_acquisition_when_data_agree
    (ranked old : Meter (LocalLoad X w)) (cache : CachedParentFrames X.site)
    (retire : J → ℕ) (go : (next : StoredSite T (nx) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) (same : ranked.result=old.result) :
    let now := openOnce ranked cache retire go bad B
    let prior := openOnce old cache retire go bad B
    (produceCacheSidecarOnce ranked.result cache).result=
      (produceCacheSidecarOnce old.result cache).result ∧
    now.result=prior.result ∧ now.steps+old.steps=prior.steps+ranked.steps := by
  cases ranked with
  | mk rk kr =>
    cases old with
    | mk ol ko =>
      dsimp only at same
      cases same
      refine ⟨rfl,rfl,?_⟩
      unfold openOnce
      dsimp only
      omega

variable {I : SiteTape sel (ticketReady T (successorTicket v w))
  (Ticket.centerAt (successorTicket v w)) (q+1)}
variable {b : ℕ} {raw : List (Word (q+1))} {i : Word b}

theorem current_raw_read_preserves_actual_header_scope_data_and_debits
    (req : Meter (Request (X:=X) (w:=w) (q:=q) I))
    (rawExact : raw.map Word.val=vectorKey sel (ticketReady T nx) (nx).centerAt I (nx).modeAt)
    (rankExact : i.val=modeOrdinal T nx)
    (legacy : Meter (Option (EventBytes (q+1) req.result.tc req.result.tz b)))
    (ok : CheckedEvent req.result.replay legacy)
    (cache : CachedParentFrames X.site) (retire : J → ℕ)
    (go : (next : StoredSite T (nx) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) :
    let rk := acceptCurrent req raw i rawExact rankExact
    let ol := acceptLocalLoad req.result.replay req.result.shell req.result.directory legacy ok
    let now := openOnce rk cache retire go bad B
    let prior := openOnce ol cache retire go bad B
    (produceCacheSidecarOnce rk.result cache).result=(produceCacheSidecarOnce ol.result cache).result ∧
    now.result=prior.result ∧ now.steps+ol.steps=prior.steps+rk.steps :=
  scope_changes_only_its_acquisition_when_data_agree _ _ cache retire go bad B
    (current_request_preserves_the_legacy_local_result req rawExact rankExact legacy ok)

#print axioms scope_changes_only_its_acquisition_when_data_agree
#print axioms current_raw_read_preserves_actual_header_scope_data_and_debits
end
end J6R68.OrdinalPeakMerge

