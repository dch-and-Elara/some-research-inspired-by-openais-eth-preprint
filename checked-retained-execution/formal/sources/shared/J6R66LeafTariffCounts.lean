import J6R66LeafTariffRegistry
import J6R66LeafTariffExterior
import J6R58LeafScaleNative

/-! Real scan geometries at the two levels of the immutable registry.
We keep the actual address-word widths, not a free unit-cost lookup. -/
namespace J6R66LeafTariff
open scoped Polynomial
open AOracleMachineTime J6R21Ancestor J6R16ModeCost J6R30ProducedGateRegistry
open J6R12Blueprint J6R11Blueprint J6R24MeteredRecursion J6ActiveRun J1PPrinted
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R48DFS J6R34RootAtlas J6R58LeafScale

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 3100

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}

theorem actual_mount_outer_lookup_capacity
    (seed : PageJob f ell key prec tw bw page) (born : Births T key prec tw bw page)
    (path : Path sel r c) (address : J6R15ModeCost.Word key) :
    let B := stackBank born (mountFromEmpty seed).result.1 path
    (locate address B.records).steps≤locateFee key (1+pathLimit s C) := by
  let B := stackBank born (mountFromEmpty seed).result.1 path
  have cap := (reached_original_mount_record_count seed born path).2
  exact (locate_bound address B.records).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (13*key+13) cap) 2)

theorem actual_native_inner_atlas_capacity (path : Path sel r c) (w : (Plan sel).Slot c)
    (I : OccurrenceInput T (path.ticket w) key prec tw bw page) :
    (compileOccurrence I).job.immutable.payload.payload.pages.length≤3*(C*s) := by
  have h := (actual_occurrence_compact_chart path w I).1
  change (compileOccurrence I).rows.length≤3*(C*s)
  exact (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0<(2:ℕ)))).trans h

theorem actual_native_inner_lookup_capacity (path : Path sel r c) (w : (Plan sel).Slot c)
    (I : OccurrenceInput T (path.ticket w) key prec tw bw page) (addr : J6R15ModeCost.Word page) :
    let pages := (compileOccurrence I).job.immutable.payload.payload.pages
    (locate addr pages).steps≤locateFee page (3*(C*s)) := by
  have cap := actual_native_inner_atlas_capacity path w I
  exact (locate_bound addr _).trans (Nat.add_le_add_right (Nat.mul_le_mul_right (13*page+13) cap) 2)

#print axioms actual_mount_outer_lookup_capacity
#print axioms actual_native_inner_atlas_capacity
#print axioms actual_native_inner_lookup_capacity
end J6R66LeafTariff
