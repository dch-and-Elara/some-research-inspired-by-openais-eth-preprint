import J6R54DispatchRetained
import J6R54DispatchLookup

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 11500000
set_option maxRecDepth 2950
set_option linter.unusedSectionVars false

/-! A small routed payload that reuses the existing checked forwarded
LocalLoad. Its raw argument is the actual external mode word; the route
is not allowed to silently substitute a different retained vector. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch J6R51Dispatch
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Slots" => ((Plan sel).Slot v.child)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

abbrev GroupRow (g : Fin 64) (raw : List (Word q)) :=
  {u : RetainedTicket X raw // u.w.val.2.2.2=g}

def MountedRows :=
  ∀ g : Fin 64,Meter (List (Σ raw : List (Word q), GroupRow X g raw))

def useMountedRows (banks : MountedRows (q:=q) X) : RetainedReader X q :=
  fun raw g =>
    let table := banks g
    let found := lookupBytes raw table.result
    ⟨found.result.map Subtype.val,table.steps+found.steps+3⟩

theorem mounted_retained_reader_paid_exact
    (banks : MountedRows (q:=q) X) (raw : List (Word q)) (g : Fin 64)
    (chosen : GroupRow X g raw)
    (before after : List (Σ w : List (Word q), GroupRow X g w))
    (held : (banks g).result=before++⟨raw,chosen⟩::after)
    (prior : ∀ e∈before,e.1≠raw) :
    useMountedRows X banks raw g =
      ⟨some chosen.val,(banks g).steps+prefixLookupFee raw before+(compareDense raw raw).steps+6⟩ := by
  have paid := prior_rows_are_paid_then_exact_same_carrier raw chosen before after prior
  unfold useMountedRows
  dsimp only
  rw [held,paid]
  dsimp only
  congr 1
  omega

#print axioms useMountedRows
#print axioms mounted_retained_reader_paid_exact
end
end J6R54Dispatch

