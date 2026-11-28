import J6R54DispatchFixedRead
import J6R54DispatchKeys

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
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
open J6R48DFS J6R49DFS A1R12 J6R22Active J6R50SourceProducer J6R51Online
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable (R : Replayed X.site w q U)
local notation "SPsrc" => (printedParams (f:=f) (ell:=ell) s)
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "rd" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "ct" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
local notation "NativePrec" => registerPrecision SPsrc v.child ct
local notation "A" => ((SPsrc).levelBits v.child.depth)
local notation "Bnk" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

/-- The exact suffix of one running probe after the current group
answers. The already-read cursor pulse is billed here only. The
reply input is a dependent-algebraic block with its actual meter. -/
def afterFixedRawReply {precision n width : ℕ} (F : Frame f precision)
    (op : Block F ell→List (Word width)→Meter (Block F ell))
    (read : List (Word width)→Fin 64→Meter (Block F ell))
    (now : Pending width n) (outer : Block F ell) (fee : ℕ)
    (raw : List (Word width)) (st : State width) (emit : now.pulse.result=.emit raw st)
    (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (reply : Meter (Block F ell)) : Meter (Block F ell) :=
  let mul := mulM F.hp ⟨inner,0⟩ reply
  let product := productCursor F.hp (read raw) left mul.result (feeM+mul.steps)
  let sum := addM F.hp ⟨outer,0⟩ product
  let rest := modeDrain op (now.tail emit) sum.result (fee+now.pulse.steps+sum.steps)
  ⟨rest.result.1,rest.steps⟩

variable {R}

theorem fixed_chart_actual_emission_enters_routed_child
    (F : J6R24MeteredRecursion.Frame f NativePrec) (I : SiteTape sel rd ct (q+1)) (live : 0<ell)
    (find : FixedPicker R) (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (retire : Job→ℕ) (go : StoredSite T nx key prec tw bw page→SM Bnk (Block F ell))
    (fallback : Meter (Block F ell)) (bank : Bnk)
    (other : List (Word (q+1))→Fin 64→Meter (Block F ell))
    (begin : Pending (q+1) I.words.length)
    (started : (startingCursor I (Nat.zero_lt_succ q)).result=some begin)
    (now : Pending (q+1) I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (updateExposed (SP:=SPsrc) (c:=v.child) (t:=ct) F live (fixedRoutedRead R find shell directory retire go fallback bank other)) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+
        (startingCursor I (Nat.zero_lt_succ q)).steps) now outer fee)
    (raw : List (Word (q+1))) (st : State (q+1)) (emit : now.pulse.result=.emit raw st)
    (g : Fin 64) (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (grown : GroupPrefix F.hp (fixedRoutedRead R find shell directory retire go fallback bank other raw)
      (oneM F.hp F.sizePos live).result (oneM F.hp F.sizePos live).steps (g::left) inner feeM)
    (cert : FixedCarrier R raw g) (chosen : (find raw g).result=some cert)
    (sameTape : cert.val.tape=I)
    (ready : JobsReady bank [(cert.val.load shell directory).result.advance.next.birth.job]) :
    let reader := fixedRoutedRead R find shell directory retire go fallback bank other
    let expected := attachReply (find raw g).steps (fixedExpected R cert shell directory retire go bank)
    decodeAt I raw=some (nx).modeAt ∧ (nx).groupAt=g ∧
    probeExposed (sel:=sel) (d:=rd) (t:=ct) F I (Nat.zero_lt_succ q) live reader =
      afterFixedRawReply F (updateExposed (SP:=SPsrc) (c:=v.child) (t:=ct) F live reader) reader now outer fee raw st emit left inner feeM expected := by
  let reader := fixedRoutedRead R find shell directory retire go fallback bank other
  have native : raw.map Word.val=vectorKey sel rd ct I (nx).modeAt := by
    rw [←sameTape]
    exact cert.val.exponents
  have realLoop := true_exposed_probe_continuation (sel:=sel) (d:=rd) (t:=ct) F I (Nat.zero_lt_succ q) live reader
    begin started now outer fee previous raw st emit g left inner feeM grown
  have selected := fixed_routed_read_opens_its_actual_child R find shell directory retire go fallback bank
    other raw g cert chosen ready
  refine ⟨literal_raw_decodes_its_key I (nx).modeAt raw native,cert.property,?_⟩
  calc
    probeExposed (sel:=sel) (d:=rd) (t:=ct) F I (Nat.zero_lt_succ q) live reader =
        afterFixedRawReply F (updateExposed (SP:=SPsrc) (c:=v.child) (t:=ct) F live reader) reader now outer fee raw st emit left inner feeM
          (reader raw g) := realLoop
    _ = _ := congrArg (afterFixedRawReply F (updateExposed (SP:=SPsrc) (c:=v.child) (t:=ct) F live reader) reader now outer fee raw st emit
      left inner feeM) selected

#print axioms fixed_chart_actual_emission_enters_routed_child
end
end J6R54Dispatch

