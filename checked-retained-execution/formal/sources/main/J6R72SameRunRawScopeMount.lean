import J6R72SameRunRawScope
import J6R68MountFilterScratchActual


/-! Use the raw interpreter's actual active branches to locate the existing mount and scope observations. These are selected local cuts, not a transfer of the old arithmetic pause or heap. -/
namespace J6R72SameRunRawScope
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute
open J6R54PeakInput J6R57ScopeFee J6R64Active J6R66Active J6R68.RecursivePeak J6R68.RetireScratch
open J6R68ActiveInputs.Sweep J6R68.MountFilterScratch J6R52Peak J6R51Peak J6R25PreparedSupply
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R16ModeCost
open J6R15ModeCost J6R50Peak J6R36ChildFramedRoute
open J6R48DFS J6R9Recursive J6R22Active J6R63Active J6R62ActivePrep J6R49DFS J6R55CachedLedger J6ActiveSchedule

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4700
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page width q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

theorem raw_active_root_evaluates_its_observed_callback
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (tails : SavedDirectoryTails width)
    (B : L) (own : OwnsHeader E.header B) (active : (S).cutoff<r.edges) :
    let ret : PageJob f ell key prec tw bw page→ℕ := retireSavedDirectory tails
    let A := rootPrepare M F chart E B own active
    let out := A.result.eval M.modeWidth (reachable_positive T (Here).reached) T.vPositive hf
      (fun t z β g=>project (observedRawReader M F chart tails B Here active t z β g).1)
    runRawRoot M F chart E ret B own=⟨(out.result,B),A.steps+out.steps⟩ := by
  dsimp only
  rw [raw_observer_projects_exactly_to_its_own_callback M F chart tails B Here active]
  exact raw_root_uses_actual_sweep M F chart E (retireSavedDirectory tails) B own active

/-- The actual active descendant mounts one resident object. Its raw-active
phase uses the exact observed callback, while the filter and frame
cuts belong to this *one* existing mount. No inherited arithmetic
suspension bound is assumed or transported. -/
theorem raw_active_descendant_mounts_and_reads_these_same_named_cuts
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (tails : SavedDirectoryTails width) (B : L) (p : Path sel r c) (u : (P).Slot c)
    (active : (S).cutoff<((P).child c u).edges) (j n : ℕ) :
    let path := Path.step p u
    let x := sourceEntered M B p u
    let ret : PageJob f ell key prec tw bw page→ℕ := retireSavedDirectory tails
    let A := afterPrepare M F chart p u x.site x.bank x.owner active
    let mounted := mountResident x.site x.resident
    let selected := observeSelection x.site.birth.native.gWord j x.site.birth.native.physical.raw
    let made := framesFromSelected x.site.site x.resident.rows selected.1.result
    let out := A.result.eval M.modeWidth (reachable_positive T path.reached) T.vPositive hf
      (fun t z β g=>project (observedRawReader M F chart tails B path active t z β g).1)
    runRawAfter M F chart ret c p u x.site x.resident x.bank x.owner=
      ⟨(out.result,x.bank),mounted.steps+A.steps+out.steps⟩ ∧
    mounted.steps=selected.1.steps+made.steps+10 ∧
    selected.2.namedPayloadBits physicalPortWords≤(sourcePhysicalBitTape x.site.input).length ∧
    unmountedChildResidentBits 0 0 M B p u+
      (((selectPorts x.site.birth.native.gWord x.site.birth.native.physical.raw).result.flatMap physicalPortWords).length+
        ((mounted.result.rows.take n).flatMap frameBits).length)≤
      recursiveResidentBits 0 M B path 0+(sourcePhysicalBitTape x.site.input).length := by
  let x := sourceEntered M B p u
  let path := Path.step p u
  let ret : PageJob f ell key prec tw bw page→ℕ := retireSavedDirectory tails
  refine ⟨?_,(actual_mount_consumes_this_single_physical_filter M B p u j).2,?_,?_⟩
  · dsimp only
    rw [raw_observer_projects_exactly_to_its_own_callback M F chart tails B path active]
    exact raw_after_uses_actual_sweep M F chart ret p u x.site x.resident x.bank x.owner active
  · exact Nat.le_of_add_le_add_left
      (actual_filter_cut_is_bounded_without_any_current_completed_frame_cache 0 0 M B p u j)
  · exact live_mount_phase_fits_one_cache_plus_real_selected_port_scratch 0 0 M B p u active n

#print axioms raw_active_root_evaluates_its_observed_callback
#print axioms raw_active_descendant_mounts_and_reads_these_same_named_cuts
end
end J6R72SameRunRawScope
