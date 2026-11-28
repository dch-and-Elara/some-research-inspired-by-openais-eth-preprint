import J6R54DispatchFixedRead

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

theorem fixed_load_exact_current_native_field_words {raw : List (Word (q+1))} {g : Fin 64}
    (cert : FixedCarrier R raw g) (shell : PayloadShell R) (directory : DirectorySeed R shell) :
    let K := (cert.val.load shell directory).result
    let native := K.event.native.result
    native.tWord.val=centerOrdinal T nx ∧ native.zWord.val=(nx).probeAt.val ∧
      native.mWord.val=modeOrdinal T nx ∧ native.gWord.val=g.val ∧
      K.event.words.result.exponents.map Word.val=liveExponentSpec R := by
  let K := (cert.val.load shell directory).result
  let native := K.event.native.result
  have tag : (nx).groupAt.val=g.val := congrArg Fin.val cert.property
  exact ⟨native.tExact,native.zExact,native.mExact,native.gExact.trans tag,K.event.acted⟩

#print axioms fixed_load_exact_current_native_field_words
end
end J6R54Dispatch

