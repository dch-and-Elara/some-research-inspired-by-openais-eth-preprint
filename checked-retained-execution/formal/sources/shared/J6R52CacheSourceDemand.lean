import J6R52CacheSourceAdvance
import J6R51OnlineVisitLocal

/-! Genuine publication of the cache-fed occurrence; the physical
replay is already the measured physical field in the job entry, so it
is not added to the outer measured local input. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R34RootAtlas J6R10Repack J6R48GeneratedAddons J6R32StatefulArithmetic J6R48DFS
open J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 9000000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def openCachedDemand {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L) : Meter (Out×L) :=
  let K := started.result
  let next := (cachedAdvance X u K cache).next
  let side := (J6R48GeneratedAddons.emit (K.directory.read X K.event)
    next.birth.native.physical.order).steps + next.site.install.steps
  let out := @J6R48DFS.withScope key prec tw bw (PagedEnvelope f ell prec page) Out retire
    next.birth.job (child next) fallback B
  ⟨out.result,(started.steps+side)+out.steps⟩

theorem open_cached_demand_exact
    {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L) :
    openCachedDemand started cache retire child fallback B=openDemand started retire child fallback B := by
  unfold openCachedDemand
  dsimp only
  rw [cached_advance_exact]
  rfl

theorem cached_visit_publishes_same_source_once
    {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L)
    (ready : JobsReady B [started.result.advance.next.birth.job]) :
    let next := (cachedAdvance X u started.result cache).next
    let j := next.birth.job
    let out := child next (afterOne B j)
    openCachedDemand started cache retire child fallback B=
      ⟨(out.result.1,B),paidAcquisition started+(publishFee B j.entry j.offset j.built+out.steps+retire j+4)⟩ := by
  rw [open_cached_demand_exact,cached_advance_exact]
  exact open_demand_from_ready started retire child fallback B ready

#print axioms open_cached_demand_exact
#print axioms cached_visit_publishes_same_source_once
end
end J6R52CacheSource
