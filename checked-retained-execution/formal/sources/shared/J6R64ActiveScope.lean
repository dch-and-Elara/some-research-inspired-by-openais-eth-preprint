import J6R64ActiveScopeKernel
import J6R52CacheWholeRun

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3200
set_option Elab.async false

/-! Same old publisher, sidecar install/mount, and retirement. A
successful continuation receives proof that the current paid header
is at the actual live head; there is no extra lookup or publication.
The dependent proof is erased and is not an additional input tape. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48GeneratedAddons J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

abbrev WithIncoming {u : Ticket sel r} (next : StoredSite T u key prec tw bw page) (Out : Type) :=
  ResidentBank next → (R : L) → OwnsHeader next.birth.job.entry.result R → Meter (Out×L)

def openWithHeader {X : StoredSite T v key prec tw bw page} {w : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X w)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v w) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) : Meter (Out×L) :=
  let K := started.result
  let next := (cachedAdvance X w K cache).next
  let made := J6R48GeneratedAddons.emit (K.directory.read X K.event) next.birth.native.physical.order
  let installed := installResidentBank next
  let out := @withScopeHeader key prec tw bw (PagedEnvelope f ell prec page) Out retire next.birth.job
    (fun cur own=>child next installed.result cur own) bad B
  ⟨out.result,(started.steps+(made.steps+installed.steps))+out.steps⟩

theorem open_header_value {X : StoredSite T v key prec tw bw page} {w : (P).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X w)) (cache : CachedParentFrames X.site)
    (retire : J→ℕ)
    (child : (next : StoredSite T (successorTicket v w) key prec tw bw page) → WithIncoming next Out)
    (old : (next : StoredSite T (successorTicket v w) key prec tw bw page) → ResidentBank next → SM L Out)
    (bad : Meter Out) (B : L)
    (same : ∀ next live R own,(child next live R own).result.1=(old next live R).result.1) :
    (openWithHeader started cache retire child bad B).result=
      (openBankDemand started cache retire old bad B).result := by
  unfold openWithHeader openBankDemand
  dsimp only
  exact scope_header_value _ _ _ _ _ _ (same _ _)

def bootWithHeader {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page) → WithIncoming next Out)
    (bad : Meter Out) (B : L) : Meter (Out×L) :=
  let start := boot.result
  let scope := @withScopeHeader key prec tw bw (PagedEnvelope f ell prec page) Out retire start.birth.job (fun cur own=>
    let loaded := installResidentBank start
    let done := child start loaded.result cur own
    ⟨done.result,loaded.steps+done.steps⟩) bad B
  ⟨scope.result,boot.steps+scope.steps⟩

theorem boot_header_value {w : (P).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page) → WithIncoming next Out)
    (old : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page) → ResidentBank next → SM L Out)
    (bad : Meter Out) (B : L)
    (same : ∀ next live R own,(child next live R own).result.1=(old next live R).result.1) :
    (bootWithHeader boot retire child bad B).result=
      (bootBankDemand boot retire old bad B).result := by
  unfold bootWithHeader bootBankDemand
  dsimp only
  exact scope_header_value _ _ _ _ _ _ (same _ _)

#print axioms open_header_value
#print axioms boot_header_value
end
end J6R64Active

