import J6R64ActiveScope
import J6R54PeakInputShare

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option maxRecDepth 3500
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Use the actual R54 one-emission sidecar as one operation, then
feed the real newly installed header to the scoped continuation.
Comparison below is equality of the full Meter, not a value-only
rewrite or an assumed tariff. -/
namespace J6R66Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48GeneratedAddons J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute
open J6R54PeakInput J6R64Active

theorem scope_same_meter_of_same_continuation {key prec tw bw : ℕ} {D Out : Type}
    (retire : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D → ℕ)
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) D)
    (go : (R : Ledger key prec tw bw D) → OwnsHeader j.entry.result R → Meter (Out×Ledger key prec tw bw D))
    (old : SM (Ledger key prec tw bw D) Out)
    (bad : Meter Out) (B : Ledger key prec tw bw D)
    (same : ∀ R own,go R own=old R) :
    withScopeHeader retire j go bad B=J6R48DFS.withScope retire j old bad B := by
  have eq : go=(fun R _=>old R) := funext (fun R=>funext (same R))
  rw [eq,scope_header_same_debit]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def openOnce {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) : Meter (Out×L) :=
  let made := produceCacheSidecarOnce started.result cache
  let next := made.result.next
  let installed := installResidentBank next
  let out := @withScopeHeader key prec tw bw (PagedEnvelope f ell prec page) Out retire next.birth.job
    (fun cur owner=>child next installed.result cur owner) bad B
  ⟨out.result,started.steps+(made.steps+installed.steps)+out.steps⟩

theorem open_once_same_full_meter {X : StoredSite T v key prec tw bw page} {u : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page) → WithIncoming next Out)
    (old : (next : StoredSite T (successorTicket v u) key prec tw bw page) → ResidentBank next → SM L Out)
    (bad : Meter Out) (B : L)
    (same : ∀ next live R own,child next live R own=old next live R) :
    openOnce started cache retire child bad B=openBankDemandSingleEmission started cache retire old bad B := by
  unfold openOnce openBankDemandSingleEmission
  dsimp only
  rw [scope_same_meter_of_same_continuation _ _ _ _ _ _ (same _ _)]

theorem boot_header_same_full_meter {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page) → WithIncoming next Out)
    (old : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page) → ResidentBank next → SM L Out)
    (bad : Meter Out) (B : L)
    (same : ∀ next live R own,child next live R own=old next live R) :
    bootWithHeader boot retire child bad B=bootBankDemand boot retire old bad B := by
  let resident := installResidentBank boot.result
  let go (R : L) (own : OwnsHeader boot.result.birth.job.entry.result R) : Meter (Out×L) :=
    let done := child boot.result resident.result R own
    ⟨done.result,resident.steps+done.steps⟩
  let prior (R : L) : Meter (Out×L) :=
    let done := old boot.result resident.result R
    ⟨done.result,resident.steps+done.steps⟩
  have agrees (R : L) (own : OwnsHeader boot.result.birth.job.entry.result R) :
      go R own=prior R := by
    dsimp only [go,prior]
    rw [same boot.result resident.result R own]
  exact congrArg (fun run : Meter (Out×L)=> (⟨run.result,boot.steps+run.steps⟩ : Meter (Out×L)))
    (scope_same_meter_of_same_continuation retire boot.result.birth.job go prior bad B agrees)

#print axioms scope_same_meter_of_same_continuation
#print axioms open_once_same_full_meter
#print axioms boot_header_same_full_meter
end
end J6R66Active

