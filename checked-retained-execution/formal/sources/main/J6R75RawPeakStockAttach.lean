import J6R75RawPeakStockCore
import J6R75RawPeakAggregate
import J6R68ActiveInputsSweepWidth

/-! The exact same active call's header, layout-copy words and mounted
mask bytes are still allowed during prepareStockFromHeader. Root
and descendant are the literal source cases of rawScheduleAt. No
caller, layout builder, or mode-tape allocator is thereby bounded. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active J6R58ActivePrep
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch J6R52FreshExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4750
set_option maxHeartbeats 10000000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def literalStockCapturesAt
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (on : (S).cutoff<x.edges) →
      Σ i, Meter (CallWords x prec i) × Meter (AtLayout sel (readyAtPath T p on) cw)
  | _,.root,on=>⟨ew,E.inherit B own,E.layout B own on⟩
  | _,.step p w,on=>
    let X := sourceState M p w
    let live := stackBank (borns M) B (.step p w)
    ⟨X.birth.edge,readIncoming X live rfl,F.layout p w X on⟩

theorem actual_raw_prepare_uses_exactly_these_stock_captures
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) :
    let input := literalStockCapturesAt M F E B own p on
    let taper := actual_path_taper T p on
    rawScheduleAt M F chart E B own p on=
      prepare M.modeWidth (F.fit p on) taper.1 taper.2 hf chart.table (chart.covers p on)
        input.2.1 input.2.2 := by
  cases p <;> rfl

def simultaneousStockInputBits {e n pw ww : ℕ} {guard : n≤2^e}
    (chart : MaskTable e n guard) (head : CallWords c pw ww) (copy : J6R15ModeCost.Word cw) (q : ℕ) : ℕ :=
  head.precision.bits.length+head.edges.bits.length+copy.bits.length+
    (retainAtWidth q copy).result.bits.length+gridMemoryBits chart.raw

theorem simultaneous_stock_input_bits_are_actual_bytes
    {e n pw ww : ℕ} {guard : n≤2^e} (chart : MaskTable e n guard)
    (head : CallWords c pw ww) (copy : J6R15ModeCost.Word cw) (q : ℕ) :
    simultaneousStockInputBits chart head copy q=pw+ww+cw+q+e*n := by
  unfold simultaneousStockInputBits
  rw [head.precision.size,head.edges.size,copy.size,(retainAtWidth q copy).result.size,
    uniform_grid_bits e chart.raw chart.width,chart.length]

/-- The actual capture is a local observation of the same installed
header and emitted layout; chart bytes are the mounted mask table only.
The caller chooses the very same ancestor resident bound from the
accepted aggregate, not an independent unmetered stored tape. -/
theorem actual_raw_path_has_one_stock_setup_with_its_named_resident
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (fit : recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p≤roof) :
    let input := literalStockCapturesAt M F E B own p on
    let words := input.2.1.result
    let layout := input.2.2.result
    let d := (rawScheduleAt M F chart E B own p on).result
    let a := (S).levelBits c.depth
    let u := (S).levelWidth c.depth
    let z := retainAtWidth q words.edges
    let t := taperRegister q u
    let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    let headers := simultaneousStockInputBits chart.table words layout.copies q
    d.stock=(prepareStockFromHeader (s:=s) M.modeWidth words).result ∧
    d.stock=(paidStockAndMargin M.modeWidth a u z.result t.result).result ∧
    (copyOfLayout q layout).result=(retainAtWidth q layout.copies).result ∧
    headers=prec+input.1+cw+q+f.natDegree*chart.count ∧
    StockCoreObservation M.modeWidth a u z.result t.result
      (resident+headers) (roof+(prec+input.1+cw+q+f.natDegree*chart.count)) := by
  let I := literalStockCapturesAt M F E B own p on
  let head := I.2.1.result
  let W := I.2.2.result
  let d := (rawScheduleAt M F chart E B own p on).result
  have hcap := simultaneous_stock_input_bits_are_actual_bytes chart.table head W.copies q
  have explicit : d.stock=(prepareStockFromHeader (s:=s) M.modeWidth head).result := by
    unfold d
    rw [actual_raw_prepare_uses_exactly_these_stock_captures]
    rfl
  refine ⟨explicit,explicit,rfl,hcap,?_⟩
  exact true_stock_producer_has_the_named_internal_phase_bounds _ _ _ _ _ _ _
    (Nat.add_le_add fit hcap.le)

#print axioms actual_raw_prepare_uses_exactly_these_stock_captures
#print axioms simultaneous_stock_input_bits_are_actual_bytes
#print axioms actual_raw_path_has_one_stock_setup_with_its_named_resident
end
end J6R75RawPeak
