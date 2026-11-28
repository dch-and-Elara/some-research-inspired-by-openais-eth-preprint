import J6R52CacheSourceDemand

/-! The actually installed indexed sidecar is retained and threaded,
rather than charging the installer and then reconstructing its result
in each continuation. -/
namespace J6R52CacheWhole
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R34RootAtlas J6R10Repack J6R48GeneratedAddons J6R32StatefulArithmetic J6R48DFS
open J6R30ProducedGateRegistry J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 9500000
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

structure ResidentBank (X : StoredSite T v key prec tw bw page) where
  rows : AddonRows X.site
  exactRows : rows=X.site.bank

def installResidentBank (X : StoredSite T v key prec tw bw page) : Meter (ResidentBank X) :=
  let done := X.site.install
  ⟨⟨done.result.getD [],rfl⟩,done.steps⟩

theorem resident_install_exact (X : StoredSite T v key prec tw bw page) :
    (installResidentBank X).result.rows=X.site.install.result.getD [] ∧
      (installResidentBank X).steps=X.site.install.steps := ⟨rfl,rfl⟩

def openBankDemand {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page)→ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L) : Meter (Out×L) :=
  let K := started.result
  let next := (cachedAdvance X u K cache).next
  let made := J6R48GeneratedAddons.emit (K.directory.read X K.event) next.birth.native.physical.order
  let installed := installResidentBank next
  let out := @J6R48DFS.withScope key prec tw bw (PagedEnvelope f ell prec page) Out retire
    next.birth.job (child next installed.result) fallback B
  ⟨out.result,(started.steps+(made.steps+installed.steps))+out.steps⟩

theorem open_bank_demand_ignorable
    {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v u) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L) :
    openBankDemand started cache retire (fun x _=>child x) fallback B=
      openDemand started retire child fallback B := by
  rw [←open_cached_demand_exact started cache retire child fallback B]
  rfl

/-- Value congruence includes both the successful and failed publication
branches; the newer continuation is allowed to incur a different fee. -/
theorem scope_return_congr {k p t b : ℕ} {D Out : Type}
    (retire : Job (key:=k) (prec:=p) (tw:=t) (bw:=b) D→ℕ)
    (j : Job (key:=k) (prec:=p) (tw:=t) (bw:=b) D)
    (go old : SM (Ledger k p t b D) Out) (bad : Meter Out) (B : Ledger k p t b D)
    (same : ∀ R,(go R).result.1=(old R).result.1) :
    (J6R48DFS.withScope retire j go bad B).result=
      (J6R48DFS.withScope retire j old bad B).result := by
  unfold J6R48DFS.withScope
  dsimp only
  split
  · rw [same]
  · rfl

theorem open_bank_demand_value
    {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page)→ResidentBank next→SM L Out)
    (old : StoredSite T (successorTicket v u) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L)
    (same : ∀ next live R,(child next live R).result.1=(old next R).result.1) :
    (openBankDemand started cache retire child fallback B).result=
      (openDemand started retire old fallback B).result := by
  rw [←open_bank_demand_ignorable started cache retire old fallback B]
  unfold openBankDemand
  dsimp only
  exact scope_return_congr _ _ _ _ _ _ (same _ _)

#print axioms resident_install_exact
#print axioms open_bank_demand_ignorable
#print axioms scope_return_congr
#print axioms open_bank_demand_value
end
end J6R52CacheWhole
