import J6R52CacheWholeBank
import J6R51OnlineVisit
import J6R25PreparedSupplyFundedActive

/-! A first exterior publication has no incoming frame cache. Its
sidecar bank is really acquired once inside the successful scope;
each later active occurrence uses the bank already returned by
its own earlier installation. -/
namespace J6R52CacheWhole
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
open J6R51ParentFrames J6R51Online J6R25PreparedSupply J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 11500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def bootBankDemand {w : (@Plan f ell s sel).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : J→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page)→
      ResidentBank next→SM L Out)
    (fallback : Meter Out) (B : L) : Meter (Out×L) :=
  let start := boot.result
  let scope := @J6R48DFS.withScope key prec tw bw (PagedEnvelope f ell prec page) Out retire
    start.birth.job (fun cur=>
      let loaded := installResidentBank start
      let done := child start loaded.result cur
      ⟨done.result,loaded.steps+done.steps⟩) fallback B
  ⟨scope.result,boot.steps+scope.steps⟩

theorem boot_bank_value {w : (@Plan f ell s sel).Slot r} {Out : Type}
    (boot : Meter (StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page))
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : (next : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page)→
      ResidentBank next→SM L Out)
    (old : StoredSite T ((Path.root : Path sel r r).ticket w) key prec tw bw page→SM L Out)
    (fallback : Meter Out) (B : L)
    (same : ∀ next live R,(child next live R).result.1=(old next R).result.1) :
    (bootBankDemand boot retire child fallback B).result=
      (bootDemand boot retire old fallback B).result := by
  unfold bootBankDemand bootDemand
  dsimp only
  exact scope_return_congr _ _ _ _ _ _ (same _ _)

def mountResident (X : StoredSite T v key prec tw bw page) (B : ResidentBank X) :
    Meter (CachedParentFrames X.site) :=
  let make := buildCache X.site B.rows B.exactRows
  let got := unwrapSuccess make (by
    obtain ⟨cache,success,_,_⟩ := built_cache_is_paid_actual_parent X.site B.rows B.exactRows
    change (buildCache X.site B.rows B.exactRows).result.isSome
    rw [success]
    rfl)
  ⟨got.result,got.steps+2⟩

theorem mounted_resident_fee (X : StoredSite T v key prec tw bw page) (B : ResidentBank X) :
    (mountResident X B).steps=(paidParentFrames X.site B.rows).steps+3+2 := by
  have ⟨_,_,price,_⟩ := built_cache_is_paid_actual_parent X.site B.rows B.exactRows
  change (buildCache X.site B.rows B.exactRows).steps+2=_
  rw [price]

theorem mounted_resident_uses_real_rows (X : StoredSite T v key prec tw bw page) (B : ResidentBank X) :
    (mountResident X B).result.rows=(childOrder X.site).map (frameOf X.site) :=
  Option.some.inj ((mountResident X B).result.exactRows.symm.trans (source_framed_in_child_order X.site))

theorem streaming_value_congr {c : Call (PhysicalHost f ell)}
    {d : Ready SP (sourceDelta s) c} {bank : Bank f}
    (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (monic : f.Monic)
    (go old : ActiveChild (sel:=sel) (d:=d) bank)
    (same : ∀ t z β g,(go t z β g).result=(old t z β g).result) :
    (D.eval hq hp hv monic go).result=(D.eval hq hp hv monic old).result := by
  exact (active_stream_value D hq hp hv monic go).trans
    ((J6R25PreparedSupply.active_result_congr (hf:=monic) hp D.prior hv go old same).trans
      (active_stream_value D hq hp hv monic old).symm)

#print axioms boot_bank_value
#print axioms mounted_resident_fee
#print axioms mounted_resident_uses_real_rows
#print axioms streaming_value_congr
end
end J6R52CacheWhole
