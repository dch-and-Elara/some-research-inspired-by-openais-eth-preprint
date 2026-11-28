import J6R53DispatchRawFields

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

set_option linter.unusedVariables false in
def FixedCarrier (raw : List (Word (q+1))) (g : Fin 64) :=
  {B : RawFields R raw // (nx).groupAt=g}

def FixedPicker :=
  ∀ (raw : List (Word (q+1))) (g : Fin 64),Meter (Option (FixedCarrier R raw g))

def attachReply {Y B : Type*} (search : ℕ) (m : Meter (Y × B)) : Meter Y :=
  ⟨m.result.1,search+m.steps+4⟩

def fixedRoutedRead {Y : Type}
    (find : FixedPicker R) (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (retire : Job→ℕ) (go : StoredSite T nx key prec tw bw page→SM Bnk Y)
    (fallback : Meter Y) (bank : Bnk)
    (other : List (Word (q+1))→Fin 64→Meter Y)
    (raw : List (Word (q+1))) (g : Fin 64) : Meter Y :=
  let first := find raw g
  match first.result with
  | none =>
    let w := other raw g
    ⟨w.result,first.steps+w.steps+3⟩
  | some cert => attachReply first.steps
    (openDemand (cert.val.load shell directory) retire go fallback bank)

def fixedExpected {Y : Type} {raw : List (Word (q+1))} {g : Fin 64}
    (cert : FixedCarrier R raw g) (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (retire : Job→ℕ) (go : StoredSite T nx key prec tw bw page→SM Bnk Y)
    (bank : Bnk) : Meter (Y×Bnk) :=
  let K := cert.val.load shell directory
  let next := K.result.advance.next
  let job := next.birth.job
  let child := go next (afterOne bank job)
  ⟨(child.result.1,bank),cert.val.dispatch.steps+6+K.result.sidecarCharge+
    (publishFee bank job.entry job.offset job.built+child.steps+retire job+4)⟩

theorem fixed_routed_read_opens_its_actual_child {Y : Type}
    (find : FixedPicker R) (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (retire : Job→ℕ) (go : StoredSite T nx key prec tw bw page→SM Bnk Y)
    (fallback : Meter Y) (bank : Bnk)
    (other : List (Word (q+1))→Fin 64→Meter Y)
    (raw : List (Word (q+1))) (g : Fin 64) (cert : FixedCarrier R raw g)
    (hit : (find raw g).result=some cert)
    (good : JobsReady bank [(cert.val.load shell directory).result.advance.next.birth.job]) :
    fixedRoutedRead R find shell directory retire go fallback bank other raw g=
      attachReply (find raw g).steps (fixedExpected R cert shell directory retire go bank) := by
  have exactScope : openDemand (cert.val.load shell directory) retire go fallback bank =
      fixedExpected R cert shell directory retire go bank :=
    RawFields.real_scoped_step (R:=R) cert.val shell directory retire go fallback bank good
  calc
    fixedRoutedRead R find shell directory retire go fallback bank other raw g =
        attachReply (find raw g).steps (openDemand (cert.val.load shell directory) retire go fallback bank) := by
      simp only [fixedRoutedRead,hit]
    _ = _ := congrArg (attachReply (find raw g).steps) exactScope

#print axioms fixedRoutedRead
#print axioms fixed_routed_read_opens_its_actual_child
end
end J6R54Dispatch

