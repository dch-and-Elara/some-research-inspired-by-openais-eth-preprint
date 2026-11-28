import J6R52CacheWholePrep
import J6R51OnlineVisitLocal

/-! Actual state and exact tariff entering a child who receives the
retained sidecar. These are local statements, not a uniform bound. -/
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
set_option maxHeartbeats 12000000
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

theorem cached_child_enters_same_paid_scope
    {X : StoredSite T v key prec tw bw page} {u : (@Plan f ell s sel).Slot v.child}
    {Out : Type} (started : Meter (LocalLoad X u)) (cache : CachedParentFrames X.site)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : (next : StoredSite T (successorTicket v u) key prec tw bw page)→ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L)
    (ready : JobsReady B [started.result.advance.next.birth.job]) :
    let next := (cachedAdvance X u started.result cache).next
    let install := installResidentBank next
    let job := next.birth.job
    let out := child next install.result (afterOne B job)
    next=started.result.advance.next ∧
    openBankDemand started cache retire child fallback B=
      ⟨(out.result.1,B),paidAcquisition started+(publishFee B job.entry job.offset job.built+
        out.steps+retire job+4)⟩ := by
  dsimp only
  rw [cached_advance_exact]
  refine ⟨rfl,?_⟩
  let go := fun next=>child next (installResidentBank next).result
  have eq : openBankDemand started cache retire child fallback B=
      openDemand started retire go fallback B :=
    open_bank_demand_ignorable started cache retire go fallback B
  rw [eq]
  exact open_demand_from_ready started retire go fallback B ready

theorem cached_boot_bank_is_paid_if_entered {w : (@Plan f ell s sel).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page)→
      ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L) (ready : JobsReady B [boot.result.birth.job]) :
    let start := boot.result
    let job := start.birth.job
    let install := installResidentBank start
    let out := child start install.result (afterOne B job)
    bootBankDemand boot retire child fallback B=
      ⟨(out.result.1,B),boot.steps+(publishFee B job.entry job.offset job.built+
         (install.steps+out.steps)+retire job+4)⟩ := by
  unfold bootBankDemand
  dsimp only
  rw [paid_scope_exact _ _ _ _ _ ready]

#print axioms cached_child_enters_same_paid_scope
#print axioms cached_boot_bank_is_paid_if_entered
end
end J6R52CacheWhole
