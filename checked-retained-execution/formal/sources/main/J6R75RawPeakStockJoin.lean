import J6R75RawPeakStockAttach
import J6R75RawPeakStockGrid
import J6R75RawPeakStockDivide

/-! One thin link from the same issued raw stock entrance to the
actual grid-construction and height-division phases, preserving its
already selected live carrier. No new time calculation. -/
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
set_option maxHeartbeats 12800000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

open J6R12CollisionMenu J6R22RootReadout

theorem actual_raw_stock_build_and_height_keep_the_same_selected_carrier
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (fit : recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p≤roof) :
    let input := literalStockCapturesAt M F E B own p on
    let words := input.2.1.result
    let layout := input.2.2.result
    let a := (S).levelBits c.depth
    let u := (S).levelWidth c.depth
    let z := (retainAtWidth q words.edges).result
    let t := (taperRegister q u).result
    let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    let headers := simultaneousStockInputBits chart.table words layout.copies q
    let held := resident+headers+((ticks a).result.length+(ticks u).result.length)
    let heightHeld := held+(gridMemoryBits (signedGridTape a).result+qBankWords (stockHeightFields M.modeWidth z t).1)
    let cap := (roof+(prec+input.1+cw+q+f.natDegree*chart.count))+stockCoreSetupRoof a u q
    let room := cap+max (3*((a+1)*2^(a+1))) (10*q+5)
    let d := (rawScheduleAt M F chart E B own p on).result
    d.stock=(paidStockAndMargin M.modeWidth a u z t).result ∧
    (∀ b,StockGridUnwind (a+1) b →
      let old := menuMachine b
      let zero := prefixMeter b false old.result
      let one := prefixMeter b true old.result
      let joined := menuMachine (b+1)
      signedGridTape a=menuMachine (a+1) ∧
      joined=⟨zero.result++one.result,
        old.steps+zero.steps+one.steps+4*old.result.length+8⟩ ∧
      held+(gridMemoryBits old.result+gridMemoryBits zero.result+
        gridMemoryBits one.result+gridMemoryBits joined.result)≤room) ∧
    (∀ (pre : List Bool) (b : Bool) (post : List Bool),
      let num := literalStockHeightNumerator M.modeWidth z t
      let den := modeWordAsA t
      num.val.reverse=pre++b::post →
      (heightWord M.modeWidth z t).result=(divideMagnitude num den).result ∧
      StockHeightDivisionCut num den pre b post heightHeld cap ∧
      cap+(10*q+5)≤room) := by
  let input := literalStockCapturesAt M F E B own p on
  let words := input.2.1.result
  let layout := input.2.2.result
  let a := (S).levelBits c.depth
  let u := (S).levelWidth c.depth
  let z := (retainAtWidth q words.edges).result
  let t := (taperRegister q u).result
  let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
  let headers := simultaneousStockInputBits chart.table words layout.copies q
  let held := resident+headers+((ticks a).result.length+(ticks u).result.length)
  let heightHeld := held+(gridMemoryBits (signedGridTape a).result+qBankWords (stockHeightFields M.modeWidth z t).1)
  let cap := (roof+(prec+input.1+cw+q+f.natDegree*chart.count))+stockCoreSetupRoof a u q
  let room := cap+max (3*((a+1)*2^(a+1))) (10*q+5)
  obtain ⟨_,stock,_,_,core⟩ :=
    actual_raw_path_has_one_stock_setup_with_its_named_resident M F chart E B own p on shared carry roof fit
  have hfit : heightHeld≤cap := core.2.2.1
  have base : held≤cap := (Nat.le_add_right _ _).trans hfit
  refine ⟨stock,?_,?_⟩
  · intro b cut
    obtain ⟨src,ran,h⟩ := actual_grid_return_holds_two_halves_and_one_result a b cut held cap base
    exact ⟨src,ran,h.trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)⟩
  · intro pre b post num den split
    obtain ⟨same,actual⟩ :=
      raw_stock_height_has_an_actual_named_restoring_cut M.modeWidth z t pre b post split
        heightHeld cap hfit
    exact ⟨same,actual,Nat.add_le_add_left (Nat.le_max_right _ _) _⟩

#print axioms actual_raw_stock_build_and_height_keep_the_same_selected_carrier
end
end J6R75RawPeak
