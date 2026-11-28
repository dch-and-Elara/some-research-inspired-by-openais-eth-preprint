import J6R110CanonicalCoverageCore
import J6R110CanonicalCoverageCost
import J6R110CanonicalMountRun
import J6R75RawPeakMaskRead

/-! Discharge only the actual chart size/scratch field for the
already-verified R110 mount. Ordered bytes are still required
for that exact instantiation, and are not inferred from capacity. -/
namespace J6R110CanonicalCoverage
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R58ActivePrep J6R62ActivePrep J6R68ActiveInputs.Sweep J6R109CanonicalProbeTable
open J6R110CanonicalMount J6R75RawPeak

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 21000000
set_option maxRecDepth 4350

noncomputable section

theorem source_root_bounds_give_positive_printed_shape
    {f : ℤ[X]} {s C : ℕ} (cfg : RootBounds s C f) : 1<s ∧ 0<f.natDegree := by
  have lp : 0<Nat.clog 2 s := by
    by_contra H
    have z : Nat.clog 2 s=0 := by omega
    have w := cfg.widthPos
    rw [z] at w
    norm_num [J9PrintedSchedule.rootU] at w
  have shape : 2^0<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mp lp
  refine ⟨by simpa only [pow_zero] using shape,?_⟩
  rw [cfg.coefficient]
  omega

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "e" => f.natDegree
local notation "d" => fullProbeDegree f.natDegree
local notation "n" => (fullProbeDegree f.natDegree+1)
local notation "fit" => full_probe_fit f.natDegree

theorem canonical_mount_coverage_from_original_prepared (T : Prepared cfg sel r hf) :
    Covers (sel:=sel) (r:=r) d :=
  fun p on=>every_active_original_call_fits_the_full_chart T p on

/-- Specialize the same existing R110 chart producer. This does
not install an additional table after that producer has returned. -/
abbrev mountFullChart (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit) : Meter (MountedChart T) :=
  mountCanonicalChart T d fit bytes (canonical_mount_coverage_from_original_prepared T)

theorem actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace
    (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit) :
    let chart := mountFullChart T bytes
    let generated := canonicalTable e n
    chart.result.count=2^e ∧
    chart.result.count≤16*s^4 ∧
    chart.result.table.raw=generated.result ∧
    chart.steps=wholeMountedDebit e (2^e) ∧
    chart.steps≤3660*s^5 ∧
    gridMemoryBits chart.result.table.raw=e*2^e ∧
    gridMemoryBits chart.result.table.raw≤128*s^5 ∧
    gridMemoryBits generated.result+gridMemoryBits chart.result.table.raw≤256*s^5 ∧
    selectedBuilderRoof e n≤264*s^5 := by
  let Builder := canonicalTable e n
  let chart := mountFullChart T bytes
  obtain ⟨hs,he⟩ := source_root_bounds_give_positive_printed_shape cfg
  have count : n=2^e := full_probe_count e
  obtain ⟨_,_,price,space,two⟩ := printed_full_chart_numeric_caps s e hs cfg.coefficient
  have card := printed_full_field_cardinality s e hs cfg.coefficient
  have bitBound := (printed_full_chart_numeric_caps s e hs cfg.coefficient).1
  obtain ⟨_,_,exactWidth⟩ := actual_canonical_table_payload_exact e d he fit
  have w : gridMemoryBits Builder.result=e*2^e := by
    change rawPayload (canonicalTable e n).result=e*2^e
    rw [show rawPayload (canonicalTable e n).result=e*n from exactWidth,count]
  obtain ⟨raw,fee⟩ := mounted_chart_is_the_paid_table_and_captured_once
    T d fit bytes (canonical_mount_coverage_from_original_prepared T) he
  have Fee : chart.steps=wholeMountedDebit e (2^e) := by
    change (mountCanonicalChart T d fit bytes (canonical_mount_coverage_from_original_prepared T)).steps=_
    rw [fee,←count]
    rfl
  have mounted : gridMemoryBits chart.result.table.raw=e*2^e := by
    change gridMemoryBits (mountCanonicalChart T d fit bytes
      (canonical_mount_coverage_from_original_prepared T)).result.table.raw=_
    rw [raw]
    exact w
  refine ⟨count,by exact count.le.trans card,raw,Fee,Fee.le.trans price,
    mounted,mounted.le.trans bitBound,?_,?_⟩
  · change gridMemoryBits Builder.result+gridMemoryBits chart.result.table.raw≤_
    rw [w,mounted]
    omega
  · rw [count]
    exact space

/-- On the unchanged R58 reader of a genuine active call, only the
literal source prefix is requested. Its encoded resident table plus
the selected copied scan words are covered by the same polynomial cap. -/
theorem actual_full_mounted_chart_keeps_its_original_active_lookup
    (T : Prepared cfg sel r hf)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d fit)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (i : Probe S c)
    (pre : List (List Bool)) (row : List Bool) (post : List (List Bool))
    (split : (mountFullChart T bytes).result.table.raw=pre++row::post) (ordinal : pre.length=i.val)
    (resident roof : ℕ) (live : resident≤roof) :
    let chart := (mountFullChart T bytes).result
    let limit := physicalProbeCount f ell s c
    let found := chart.table.readRaw (chart.covers p on) i
    let actual := copyBits row
    let scan := (pre.map copyBits).foldr resumeMaskScan ⟨some actual.result,actual.steps+4⟩
    found=⟨List.ofFn (NativeProbeRing.chosenRep e limit (readyAtPath T p on).fit i),
      (i.val+1)*(3*e+5)⟩ ∧
    found=⟨actual.result,scan.steps⟩ ∧
    found.steps≤464*s^5 ∧
    resident+(gridMemoryBits chart.table.raw+gridMemoryBits (pre.map (fun x=>(copyBits x).result))+
      actual.result.length)≤roof+256*s^5 := by
  let chart := (mountFullChart T bytes).result
  obtain ⟨hs,_⟩ := source_root_bounds_give_positive_printed_shape cfg
  obtain ⟨_,copyRate,_,_,two⟩ := printed_full_chart_numeric_caps s e hs cfg.coefficient
  have count : n=2^e := full_probe_count e
  have size : i.val+1≤n :=
    (Nat.succ_le_of_lt i.isLt).trans (every_active_original_call_fits_the_full_chart T p on)
  have old := full_chart_serves_the_unchanged_original_probe_index T chart.table p on i
  have held := mounted_mask_addressed_copy_keeps_the_same_named_table_bytes
    chart.table (chart.covers p on) i pre row post split ordinal resident roof live
  have pointFee : (i.val+1)*(3*e+5)≤464*s^5 :=
    (Nat.mul_le_mul_right _ (size.trans_eq count)).trans copyRate
  have localBytes : e*n+e*(i.val+1)≤256*s^5 := by
    calc
      _ ≤ e*n+e*n := Nat.add_le_add_left (Nat.mul_le_mul_left e size) _
      _ = 2*(e*2^e) := by rw [count]; omega
      _ ≤ _ := two
  refine ⟨old.1,held.2.1,?_,held.2.2.trans (Nat.add_le_add_left localBytes _)⟩
  change (chart.table.readRaw (chart.covers p on) i).steps≤_
  rw [old.1]
  exact pointFee

#print axioms source_root_bounds_give_positive_printed_shape
#print axioms canonical_mount_coverage_from_original_prepared
#print axioms actual_full_mount_has_one_printed_polynomial_fee_and_selected_workspace
#print axioms actual_full_mounted_chart_keeps_its_original_active_lookup
end
end J6R110CanonicalCoverage
