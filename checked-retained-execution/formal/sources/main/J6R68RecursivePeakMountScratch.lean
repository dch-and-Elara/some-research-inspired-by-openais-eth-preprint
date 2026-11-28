import J6R68RecursivePeakBound
import J6R68RecursivePeakVisit
import J6R54PeakInputOccurrence

/-! While mounting the child's true cached frame rows, the selected
raw-port subset is an extra view of the still resident physical tape.
Use the current cache reserve for its own prefix; do not charge a
completed current cache plus its not-yet-completed copy. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R51ParentFrames J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS J6R36ChildFramedRoute J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4510
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 6500000
set_option Elab.async false

private theorem selected_list_width_le {A : Type*}
    (xs : List A) (pred : A→Bool) (code : A→List Bool) :
    ((xs.filter pred).flatMap code).length≤(xs.flatMap code).length := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    by_cases picked : pred x=true
    · simp only [List.filter_cons,picked,if_true,List.flatMap_cons,List.length_append]
      exact Nat.add_le_add_left ih _
    · have no : pred x=false := Bool.eq_false_of_not_eq_true picked
      simp only [List.filter_cons,no,Bool.false_eq_true,if_false,List.flatMap_cons,List.length_append]
      exact ih.trans (Nat.le_add_left _ _)

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)

def unmountedChildResidentBits (shared paused : ℕ)
    (M : OnlineMachine T key prec tw bw page q) (B : L)
    (p : Path sel r c) (w : (P).Slot c) : ℕ :=
  let next := Path.step p w
  shared+paused+mountedSelectedBits (stackBank (borns M) B next)+
    (physicalInputStackBits M next+(rawStackBits M next+addonStackBits M next+cacheStackBits M p))

theorem actual_entered_uses_its_billed_mounted_cache
    (M : OnlineMachine T key prec tw bw page q) (B : L)
    (p : Path sel r c) (w : (P).Slot c) :
    let entered := sourceEntered M B p w
    mountResident entered.site entered.resident=sourceMounted (M:=M) p w := rfl

theorem live_mount_phase_fits_one_cache_plus_real_selected_port_scratch
    (shared paused : ℕ) (M : OnlineMachine T key prec tw bw page q) (B : L)
    (p : Path sel r c) (w : (P).Slot c) (active : (S).cutoff<((P).child c w).edges) (n : ℕ) :
    let entered := sourceEntered M B p w
    let picked := selectPorts entered.site.birth.native.gWord entered.site.birth.native.physical.raw
    let mounting := mountResident entered.site entered.resident
    unmountedChildResidentBits shared paused M B p w+
        ((picked.result.flatMap physicalPortWords).length+((mounting.result.rows.take n).flatMap frameBits).length)≤
      recursiveResidentBits shared M B (.step p w) paused+
        (sourcePhysicalBitTape entered.site.input).length := by
  let X := sourceState M p w
  let mounted := sourceMounted (M:=M) p w
  let without := unmountedChildResidentBits shared paused M B p w
  have joined :
      recursiveResidentBits shared M B (.step p w) paused=without+(cachedWireBits mounted.result).length := by
    change recursiveResidentBits shared M B (.step p w) paused=
      unmountedChildResidentBits shared paused M B p w+(cachedWireBits mounted.result).length
    unfold recursiveResidentBits unmountedChildResidentBits cachedIngressBits
    simp only [cacheStackBits,actualMountedFields,if_pos active]
    dsimp only [mounted]
    ac_rfl
  rw [joined]
  let selected := selectPorts X.birth.native.gWord X.birth.native.physical.raw
  have subset :
      (selected.result.flatMap physicalPortWords).length≤(sourcePhysicalBitTape X.input).length := by
    have real := compiled_occurrence_uses_same_physical_port_tape X.input
    change X.birth.native.physical.raw.flatMap physicalPortWords=sourcePhysicalBitTape X.input at real
    rw [←real]
    unfold selected
    rw [(select_ports_exact X.birth.native.gWord X.birth.native.physical.raw).1]
    exact selected_list_width_le _ _ _
  have made :
      ((mounted.result.rows.take n).flatMap frameBits).length≤(cachedWireBits mounted.result).length :=
    encoded_take_le_full mounted.result.rows frameBits n
  have h := Nat.add_le_add_left (Nat.add_le_add subset made) without
  exact h.trans_eq (by
    change without+((sourcePhysicalBitTape X.input).length+(cachedWireBits mounted.result).length)=
      without+(cachedWireBits mounted.result).length+(sourcePhysicalBitTape X.input).length
    rw [Nat.add_comm (sourcePhysicalBitTape X.input).length,Nat.add_assoc])

theorem mount_extra_is_bounded_by_that_parent_source_extent
    (shared paused : ℕ) {cw ew : ℕ}
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (fixed addr seed : ℕ) (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (p : Path sel r c) (w : (P).Slot c) (active : (S).cutoff<((P).child c w).edges) (n : ℕ) :
    let entered := sourceEntered M B p w
    let picked := selectPorts entered.site.birth.native.gWord entered.site.birth.native.physical.raw
    let mounting := mountResident entered.site entered.resident
    unmountedChildResidentBits shared paused M B p w+
        ((picked.result.flatMap physicalPortWords).length+((mounting.result.rows.take n).flatMap frameBits).length)≤
      recursiveResidentBits shared M B (.step p w) paused+(2*c.edges)*(addr+sourceBodyCap s C seed) := by
  have bound := actual_demanded_occurrence_port_bits_uniform (shadow M F E B own) fixed addr seed sizes boot p w
  rw [shadow_stored_sites_unchanged] at bound
  exact (live_mount_phase_fits_one_cache_plus_real_selected_port_scratch shared paused M B p w active n).trans
    (Nat.add_le_add_left bound _)

#print axioms mount_extra_is_bounded_by_that_parent_source_extent

#print axioms actual_entered_uses_its_billed_mounted_cache
#print axioms live_mount_phase_fits_one_cache_plus_real_selected_port_scratch
end
end J6R68.RecursivePeak