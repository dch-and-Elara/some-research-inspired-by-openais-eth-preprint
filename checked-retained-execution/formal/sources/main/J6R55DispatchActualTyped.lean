import J6R55DispatchPaid
import J6R54DispatchFixedRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8500000
set_option Elab.async false
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false

/-! A descendant dispatch is bound to the precise `readAfter`
callback of the online machine. The equality hypothesis is only the
selected local acquisition meter, not a supplied value, child run,
or publication tariff. -/
namespace J6R55Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R25PreparedSupply J6R34ChildPath J6R49DFS
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS J6R51Online
open J6R50SourceProducer J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R51Dispatch J6R16ModeCost
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
private abbrev activeAt
    (T : Prepared cfg sel root hf) {parent : Call (PhysicalHost f ell)}
    (p : Path sel root parent) (u : (Plan sel).Slot parent)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child parent u).edges) :=
  ready_reachable cfg sel (Path.step p u).reached T.rootStable on

private abbrev frameAt
    (T : Prepared cfg sel root hf) {parent : Call (PhysicalHost f ell)}
    (p : Path sel root parent) (u : (Plan sel).Slot parent)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child parent u).edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u)) :=
  T.bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u) t)
    (register_positive (activeAt T p u on) t)

private abbrev slotAt
    (T : Prepared cfg sel root hf) {parent : Call (PhysicalHost f ell)}
    (p : Path sel root parent) (u : (Plan sel).Slot parent)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child parent u).edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u))
    (z : Probe (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u))
    (β : NativeMenu (N sel) ((Plan sel).child parent u) t) (g : Fin 64) :=
  addressed (sel:=sel) (activeAt T p u on) t z β g

/-! Actual `OnlineMachine` pulse and actual `readAfter` invocation.
The raw comparison supplies a whole paid acquisition, and no second
cursor pulse appears in the load or the resumed arithmetic operation. -/
theorem real_typed_probe_scope_uses_its_emission
    {parent : Call (PhysicalHost f ell)} (p : Path sel root parent) (u : (Plan sel).Slot parent)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<((Plan sel).child parent u).edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u))
    (z : Probe (printedParams (f:=f) (ell:=ell) s) ((Plan sel).child parent u))
    (β : NativeMenu (N sel) ((Plan sel).child parent u) t) (g : Fin 64)
    {q : ℕ} {U : ExplicitSelectedWords X.site (slotAt T p u on t z β g) q}
    (R : Replayed X.site (slotAt T p u on t z β g) q U)
    (M : OnlineMachine T key prec tw bw page (q+1))
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (bank : PageBank f ell key prec tw bw page)
    (live : 0<ell) (vraw : List (Word (q+1)))
    (find : FixedPicker R) (cert : FixedCarrier R vraw g)
    (picked : (find vraw g).result=some cert)
    (shell : PayloadShell R) (directory : DirectorySeed R shell)
    (other : List (Word (q+1))→Fin 64→Meter (Block (frameAt T p u on t) ell))
    (paid : M.demand X (slotAt T p u on t z β g)=mountedDemand R find cert shell directory)
    (good : JobsReady bank [(cert.val.load shell directory).result.advance.next.birth.job])
    (I : SiteTape sel (activeAt T p u on) t (q+1))
    (actualTape : I=((M.activeAfter p u X on).result.tape t).tape.result)
    (sameTape : HEq cert.val.tape I)
    (begin : Pending (q+1) I.words.length)
    (start : (startingCursor I (Nat.zero_lt_succ q)).result=some begin)
    (now : Pending (q+1) I.words.length) (outer : Block (frameAt T p u on t) ell) (fee : ℕ)
    (prev :
      let F := frameAt T p u on t
      ModePrefix (modeUpdate F I live (readAfter M retire p u X on bank t z)) begin
        (zeroM (ell:=ell) (f:=F.words) F.hp).result
        ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I (Nat.zero_lt_succ q)).steps)
        now outer fee)
    (st : State (q+1)) (emit : now.pulse.result=.emit vraw st)
    (left : List (Fin 64)) (inner : Block (frameAt T p u on t) ell) (feeM : ℕ)
    (grown :
      let F := frameAt T p u on t
      GroupPrefix F.hp (readAfter M retire p u X on bank t z β)
        (oneM F.hp F.sizePos live).result (oneM F.hp F.sizePos live).steps (g::left) inner feeM) :
    let F := frameAt T p u on t
    let old := readAfter M retire p u X on bank t z
    let run := runAfter M retire ((Plan sel).child parent u) (Path.step p u) (slotAt T p u on t z β g)
    let step := attachReply (find vraw g).steps (fixedExpected R cert shell directory retire run bank)
    runProbe F (((M.activeAfter p u X on).result.tape t).tape.result) (Nat.zero_lt_succ q) live old =
      afterFixedRawReply F (modeUpdate F I live old) (fun _=>old β) now outer fee vraw st emit
        left inner feeM step := by
  let F := frameAt T p u on t
  let d := activeAt T p u on
  let old := readAfter M retire p u X on bank t z
  let run := runAfter M retire ((Plan sel).child parent u) (Path.step p u) (slotAt T p u on t z β g)
  have Same : cert.val.tape=I := eq_of_heq sameTape
  have vals : vraw.map Word.val=vectorKey sel d t I β := by
    rw [←Same]
    exact cert.val.exponents
  have H := literal_raw_decodes_its_key I β vraw vals
  have chosen : fixedRoutedRead R find shell directory retire run (zeroM F.hp) bank other vraw g=old β g := by
    have e := observed_route_is_actual_demand_meter R find cert picked shell directory
      retire run (zeroM F.hp) bank other
    apply e.trans
    exact congrArg (fun L=>project (openDemand L retire run (zeroM F.hp) bank)) paid.symm
  have scope := fixed_routed_read_opens_its_actual_child R find shell directory retire
    run (zeroM F.hp) bank other vraw g cert picked good
  have call := chosen.symm.trans scope
  have actual := probe_halts_after_actual_child F I (Nat.zero_lt_succ q) live old
    begin start now outer fee prev vraw st emit β H g left inner feeM grown
  dsimp only
  calc
    runProbe F ((M.activeAfter p u X on).result.tape t).tape.result (Nat.zero_lt_succ q) live old =
      runProbe F I (Nat.zero_lt_succ q) live old := by rw [actualTape]
    _ = afterFixedRawReply F (modeUpdate F I live old) (fun _=>old β) now outer fee vraw st emit
        left inner feeM (old β g) := actual
    _ = _ := congrArg (afterFixedRawReply F (modeUpdate F I live old) (fun _=>old β)
      now outer fee vraw st emit left inner feeM) call

#print axioms real_typed_probe_scope_uses_its_emission
end
end J6R55Dispatch
