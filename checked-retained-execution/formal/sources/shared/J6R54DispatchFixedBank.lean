import J6R54DispatchFixedRead
import J6R54DispatchLookup

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! Paste the actual emitted raw byte vector into the descendant
allocator directly, without re-running a cursor. A discovery input
selects current local shell/geometry and has a visible Meter; it is
not allowed to return a precomputed child. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R51Dispatch J6R52Dispatch J6R53Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R48DFS J6R50SourceProducer J6R51Online
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable (R : Replayed X.site w q U)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "d" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "t" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
local notation "A" => ((SP).levelBits v.child.depth)
local notation "Bnk" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

def MountedFixedRows :=
  ∀ g : Fin 64, Meter (List (Σ raw : List (Word (q+1)), FixedCarrier R raw g))

def chooseMountedFixed (bins : MountedFixedRows R) : FixedPicker R :=
  fun raw g =>
    let mounted := bins g
    let scan := lookupBytes raw mounted.result
    ⟨scan.result,mounted.steps+scan.steps+3⟩

theorem mounted_fixed_reader_paid_and_exact
    (bins : MountedFixedRows R) (raw : List (Word (q+1))) (g : Fin 64)
    (U : FixedCarrier R raw g)
    (before after : List (Σ row : List (Word (q+1)), FixedCarrier R row g))
    (held : (bins g).result=before++⟨raw,U⟩::after)
    (first : ∀ E∈before,E.1≠raw) :
    chooseMountedFixed R bins raw g =
      ⟨some U,(bins g).steps+prefixLookupFee raw before+
        (compareDense raw raw).steps+6⟩ := by
  have paid := prior_rows_are_paid_then_exact_same_carrier raw U before after first
  unfold chooseMountedFixed
  dsimp only
  rw [held,paid]
  dsimp only
  congr 1
  omega

#print axioms chooseMountedFixed
#print axioms mounted_fixed_reader_paid_and_exact
end
end J6R54Dispatch

