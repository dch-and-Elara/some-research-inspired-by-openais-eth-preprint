import J6R75RawPeakCarry
import J6R72SameRunLocalPeak
import J6R72SameRunRawScopeMount

/-! Keep the very same raw suspended ancestor fields across the actual
child's publication, physical mount, and return. The local cuts are
different phases, with maximum rather than additive scratch. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R68.RetireScratch J6R68.MountFilterScratch J6R72SameRunLocalPeak J6R72SameRunRawScope
open J6R51ParentFrames J6R52CacheWhole J6R52CacheSource J6R25PreparedSupply

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4700
set_option maxHeartbeats 4900000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)

def trueRawReturnWithCarry (M : Machine) (B : L)
    (p : Path sel r c) (w : (P).Slot c) (shared carry : ℕ)
    (words : TailCopyObservation width) : ℕ :=
  let next := Path.step p w
  selectedRetireOverlap (shared+carry+cachedIngressBits M next) (stackBank (borns M) B next) words

private theorem no_mounted_output_is_below_resident_bits
    (M : Machine) (B : L) (shared carry : ℕ) (p : Path sel r c) (w : (P).Slot c) :
    unmountedChildResidentBits shared carry M B p w≤recursiveResidentBits shared M B (.step p w) carry := by
  unfold unmountedChildResidentBits recursiveResidentBits cachedIngressBits
  simp only [cacheStackBits]
  exact Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_right _ _) _) _) _

theorem real_raw_child_scope_phases_keep_one_and_the_same_ancestor_payload
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64)
    (carry : ℕ)
    (seen : ActualRawAncestorStack M F chart E B own tails
      (.step p (addressed (sel:=sel) (readyAtPath T p a) t z β g)) carry) :
    let w := addressed (sel:=sel) (readyAtPath T p a) t z β g
    let obs := observedRawReader M F chart tails B p a t z β g
    let roof := rawCarrierRoof shared B r pageBound fixed addr seed owner s C q
    let room := roof+max ((2*(C*s))*(addr+sourceBodyCap s C seed)) (4*width)
    project obs.1=rawReaderAt M F chart (retireSavedDirectory tails) B p a t z β g ∧
      obs.2=some ⟨tails,tails⟩ ∧ obs.1.result.2=stackBank (borns M) B p ∧
    trueRawReturnWithCarry M B p w shared carry ⟨tails,tails⟩≤room ∧
    (∀ point,recursiveStagingBits M B p w shared carry point≤roof) ∧
    (∀ (_active : (S).cutoff<((P).child c w).edges) (j n : ℕ) (point : ChildWritePoint),
      let x := sourceEntered M B p w
      let picked := observeSelection x.site.birth.native.gWord j x.site.birth.native.physical.raw
      let wrote := framesFromSelected x.site.site x.resident.rows picked.1.result
      (mountResident x.site x.resident).steps=picked.1.steps+wrote.steps+10 ∧
      max (recursiveStagingBits M B p w shared carry point)
        (max (max (filterBits M B p w shared carry j) (framePrefixBits M B p w shared carry n))
          (trueRawReturnWithCarry M B p w shared carry (⟨tails,tails⟩ : TailCopyObservation width)))≤room) := by
  let w := addressed (sel:=sel) (readyAtPath T p a) t z β g
  let next := Path.step p w
  let base := recursiveResidentBits shared M B next carry
  let roof := rawCarrierRoof shared B r pageBound fixed addr seed owner s C q
  let extra := (2*(C*s))*(addr+sourceBodyCap s C seed)
  let room := roof+max extra (4*width)
  have entered : base≤roof := raw_ancestor_and_same_physical_carrier_fit_together
    M F chart E B own tails shared pageBound fixed addr seed owner pageFit sizes boot owners next carry seen
  have pub (point : ChildWritePoint) : recursiveStagingBits M B p w shared carry point≤roof :=
    (suspended_parent_plus_staging_fits_the_actual_child_reserve M B p w shared carry point).trans entered
  have retEq :
      trueRawReturnWithCarry M B p w shared carry (⟨tails,tails⟩ : TailCopyObservation width)=base+4*width := by
    unfold trueRawReturnWithCarry selectedRetireOverlap base recursiveResidentBits
    rw [observed_source_and_copy_are_four_words]
    dsimp only [next]
    ac_rfl
  have ret : trueRawReturnWithCarry M B p w shared carry (⟨tails,tails⟩ : TailCopyObservation width)≤room := by
    rw [retEq]
    exact Nat.add_le_add entered (Nat.le_max_right _ _)
  obtain ⟨read,words,state⟩ :=
    actual_raw_reader_returns_through_its_own_saved_tail_cut M F chart tails B legal p a t z β g
  refine ⟨read,words,state,ret,pub,?_⟩
  intro active j n point
  have sourceRoom : (sourcePhysicalBitTape (sourceState M p w).input).length≤extra :=
    (actual_demanded_occurrence_port_bits_uniform M fixed addr seed sizes boot p w).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (actual_edges_uniform T p)))
  have cut0 := actual_filter_cut_is_bounded_without_any_current_completed_frame_cache shared carry M B p w j
  have frame0 := live_mount_phase_fits_one_cache_plus_real_selected_port_scratch shared carry M B p w active n
  have sel : filterBits M B p w shared carry j≤base+extra :=
    cut0.trans (Nat.add_le_add (no_mounted_output_is_below_resident_bits M B shared carry p w) sourceRoom)
  have nr : framePrefixBits M B p w shared carry n≤base+extra :=
    frame0.trans (Nat.add_le_add_left sourceRoom _)
  have bound : base+extra≤room := Nat.add_le_add entered (Nat.le_max_left _ _)
  exact ⟨(actual_mount_consumes_this_single_physical_filter M B p w j).2,
    Nat.max_le.mpr ⟨(pub point).trans (Nat.le_add_right _ _),
      Nat.max_le.mpr ⟨(Nat.max_le.mpr ⟨sel,nr⟩).trans bound,ret⟩⟩⟩

#print axioms real_raw_child_scope_phases_keep_one_and_the_same_ancestor_payload
end
end J6R75RawPeak
