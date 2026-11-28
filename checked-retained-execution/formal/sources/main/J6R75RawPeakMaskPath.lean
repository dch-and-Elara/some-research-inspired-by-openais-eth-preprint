import J6R75RawPeakStockAttach
import J6R75RawPeakMaskRead

/-! On the very emitted raw active centre the local mask is a
literal scan of the already mounted row table. Keep the same path
carrier and issued stock, without replacing the probe provider. -/
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
set_option maxHeartbeats 17500000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

theorem same_raw_emitted_masks_are_the_actual_installed_table_reads
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) :
    let D := (rawScheduleAt M F chart E B own p on).result
    ∀ (x : D.EmitRow) (z : Probe S c),
      let mask := (D.fetch x).masks z
      (⟨mask.result.val,mask.steps⟩ : Meter (List Bool))=
        chart.table.readRaw (chart.covers p on) z := by
  cases p <;> intro D x z <;> rfl

theorem actual_raw_probe_lookup_keeps_its_stock_and_same_ancestor_words
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (fits : recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p≤roof) :
    let D := (rawScheduleAt M F chart E B own p on).result
    let preset := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    ∀ (x : D.EmitRow) (z : Probe S c) (pre : List (List Bool)) (row : List Bool) (post : List (List Bool)),
      chart.table.raw=pre++row::post → pre.length=z.val →
    let mask := (D.fetch x).masks z
    let copy := copyBits row
    let seen := (pre.map copyBits).foldr resumeMaskScan ⟨some copy.result,copy.steps+4⟩
    (⟨mask.result.val,mask.steps⟩ : Meter (List Bool))=⟨copy.result,seen.steps⟩ ∧
    preset+rawStockBits D.stock+
      (gridMemoryBits chart.table.raw+gridMemoryBits (pre.map (fun x=>(copyBits x).result))+copy.result.length)≤
    roof+rawStockBits D.stock+(f.natDegree*chart.count+f.natDegree*(z.val+1)) := by
  intro D preset x z pre row post split ordinal
  have same := same_raw_emitted_masks_are_the_actual_installed_table_reads M F chart E B own p on x z
  obtain ⟨_,seen,cap⟩ := mounted_mask_addressed_copy_keeps_the_same_named_table_bytes chart.table
    (chart.covers p on) z pre row post split ordinal
    (preset+rawStockBits D.stock) (roof+rawStockBits D.stock) (Nat.add_le_add_right fits _)
  exact ⟨same.trans seen,cap⟩

#print axioms same_raw_emitted_masks_are_the_actual_installed_table_reads
#print axioms actual_raw_probe_lookup_keeps_its_stock_and_same_ancestor_words
end
end J6R75RawPeak
