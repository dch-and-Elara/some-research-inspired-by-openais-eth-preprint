import J6R110CanonicalCoverageMount
import J6R75RawPeakMaskPath

/-! Keep the exact old raw sweep's live carrier and stock while its
real emitted probe consumes the paid full chart. This is an attachment
to the source callback, not an estimate for an arbitrary lookup. -/
namespace J6R110CanonicalCoverage
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active J6R58ActivePrep
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch J6R52FreshExterior
open J6R75RawPeak J6R110CanonicalMount J6R109CanonicalProbeTable

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxHeartbeats 17500000
set_option maxRecDepth 4750

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "e" => f.natDegree
local notation "d" => fullProbeDegree f.natDegree
local notation "n" => (fullProbeDegree f.natDegree+1)
local notation "fit" => full_probe_fit f.natDegree

theorem exact_raw_path_reads_the_paid_full_table_in_its_existing_stock_room
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (fits : recursiveResidentBits shared M B p carry+
      exactAncestorJetWidth M F (mountFullChart T bytes).result E B own p≤roof) :
    let chart := (mountFullChart T bytes).result
    let D := (rawScheduleAt M F chart E B own p on).result
    let saved := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    ∀ (x : D.EmitRow) (z : Probe S c) (pre : List (List Bool)) (row : List Bool) (post : List (List Bool)),
      chart.table.raw=pre++row::post → pre.length=z.val →
      let mask := (D.fetch x).masks z
      let copy := copyBits row
      let seen := (pre.map copyBits).foldr resumeMaskScan ⟨some copy.result,copy.steps+4⟩
      (⟨mask.result.val,mask.steps⟩ : Meter (List Bool))=⟨copy.result,seen.steps⟩ ∧
      mask.steps≤464*s^5 ∧
      saved+rawStockBits D.stock+
        (gridMemoryBits chart.table.raw+gridMemoryBits (pre.map (fun w=>(copyBits w).result))+copy.result.length)≤
      roof+rawStockBits D.stock+256*s^5 := by
  intro chart D saved x z pre row post split index
  have exactCall := same_raw_emitted_masks_are_the_actual_installed_table_reads M F chart E B own p on x z
  have paid := actual_full_mounted_chart_keeps_its_original_active_lookup T bytes p on z pre row post
    split index (saved+rawStockBits D.stock) (roof+rawStockBits D.stock) (Nat.add_le_add_right fits _)
  have stamp := congrArg (fun t : Meter (List Bool)=>t.steps) exactCall
  exact ⟨exactCall.trans paid.2.1,stamp.le.trans paid.2.2.1,paid.2.2.2⟩

#print axioms exact_raw_path_reads_the_paid_full_table_in_its_existing_stock_room
end
end J6R110CanonicalCoverage
