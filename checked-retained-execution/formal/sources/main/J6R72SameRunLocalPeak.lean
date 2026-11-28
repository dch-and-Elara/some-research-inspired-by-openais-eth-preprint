import J6R72SameRunLocalPeakScope
import J6R68MountFilterScratchActual
import J6R68RecursivePeakTotal

/-! Selected physical phases of one existing R66 transition.
At a filter cut the current frame output has not been made. At a
frame-write cut only the built prefix is counted. At retirement
the returned child bank can conservatively remain in the reserve.
These are different phases; take their maximum, never their sum. -/
namespace J6R72SameRunLocalPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R21Ancestor
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R51ParentFrames J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
open J6R63Active J6R64Active J6R66Active J6R49DFS J6R36ChildFramedRoute J6R25PreparedSupply
open J6R68.RecursivePeak J6R68.MountFilterScratch J6R68.RetireScratch J6R52CacheSource
open J6R57ScopeFee J6R9Recursive

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4700
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def filterBits (M : Machine) (B : L) (p : Path sel r c) (w : (P).Slot c)
    (shared buf : ℕ) (j : ℕ) : ℕ :=
  let x := sourceEntered M B p w
  let cut := (observeSelection x.site.birth.native.gWord j x.site.birth.native.physical.raw).2
  unmountedChildResidentBits shared buf M B p w+cut.namedPayloadBits physicalPortWords

def framePrefixBits (M : Machine) (B : L) (p : Path sel r c) (w : (P).Slot c)
    (shared buf : ℕ) (j : ℕ) : ℕ :=
  let x := sourceEntered M B p w
  let picked := selectPorts x.site.birth.native.gWord x.site.birth.native.physical.raw
  let mounting := mountResident x.site x.resident
  unmountedChildResidentBits shared buf M B p w+
    ((picked.result.flatMap physicalPortWords).length+((mounting.result.rows.take j).flatMap frameBits).length)

/-- A conservative envelope at the observed return, not an assertion that
every child source field is still allocated. The directory is the actual
live one, and the additional fields are the two pairs of copied words. -/
def retireBits (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (w : (P).Slot c) (shared buf roster : ℕ)
    (obs : TailCopyObservation width) : ℕ :=
  let next := Path.step p w
  let held := shared+buf+cachedIngressBits M next+literalControlPath M F E B own next+roster
  selectedRetireOverlap held (stackBank (borns M) B next) obs

def localPeakRoof (residentRoof s C addr seed width : ℕ) : ℕ :=
  residentRoof+max ((2*(C*s))*(addr+sourceBodyCap s C seed)) (4*width)

private theorem unmounted_le_live (shared buf : ℕ) (M : Machine) (B : L)
    (p : Path sel r c) (w : (P).Slot c) :
    unmountedChildResidentBits shared buf M B p w≤recursiveResidentBits shared M B (.step p w) buf := by
  unfold unmountedChildResidentBits recursiveResidentBits cachedIngressBits
  simp only [cacheStackBits]
  exact Nat.add_le_add_left
    (Nat.add_le_add_left (Nat.add_le_add_left (Nat.le_add_right _ _) _) _) _

theorem return_cut_fits_existing_reserve_plus_two_pairs
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (w : (P).Slot c) (shared buf roster : ℕ)
    (obs : TailCopyObservation width) :
    retireBits M F E B own p w shared buf roster obs=
      recursiveResidentBits shared M B (.step p w) buf+
        literalControlPath M F E B own (.step p w)+roster+4*width := by
  unfold retireBits selectedRetireOverlap recursiveResidentBits
  rw [observed_source_and_copy_are_four_words]
  dsimp only
  ac_rfl

theorem existing_live_path_bounds_mount_and_retirement_by_a_max
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (fixed addr seed shared buf roster roof : ℕ)
    (sizes : EntryWidths (shadow M F E B own) fixed addr)
    (boot : BootBodyWidth (shadow M F E B own) seed)
    (p : Path sel r c) (w : (P).Slot c)
    (base : recursiveResidentBits shared M B (.step p w) buf+
       literalControlPath M F E B own (.step p w)+roster≤roof)
    (obs : TailCopyObservation width) :
    retireBits M F E B own p w shared buf roster obs≤localPeakRoof roof s C addr seed width ∧
      ∀ (_live : (S).cutoff<((P).child c w).edges) (j n : ℕ),
        let x := sourceEntered M B p w
        let picked := observeSelection x.site.birth.native.gWord j x.site.birth.native.physical.raw
        let wrote := framesFromSelected x.site.site x.resident.rows picked.1.result
        (mountResident x.site x.resident).steps=picked.1.steps+wrote.steps+10 ∧
        max (max (filterBits M B p w shared buf j)
                 (framePrefixBits M B p w shared buf n)+
          literalControlPath M F E B own (.step p w)+roster)
          (retireBits M F E B own p w shared buf roster obs)≤localPeakRoof roof s C addr seed width := by
  let delta := (2*(C*s))*(addr+sourceBodyCap s C seed)
  let H := localPeakRoof roof s C addr seed width
  have Ebound : (2*c.edges)*(addr+sourceBodyCap s C seed) ≤ delta :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (actual_edges_uniform T p))
  have ret : retireBits M F E B own p w shared buf roster obs≤H := by
    rw [return_cut_fits_existing_reserve_plus_two_pairs]
    exact Nat.add_le_add base (Nat.le_max_right delta _)
  refine ⟨ret,?_⟩
  intro live j n
  have cut := actual_filter_cut_has_the_same_parent_extent_bound shared buf M F E B own
    fixed addr seed sizes boot p w j
  have frames := mount_extra_is_bounded_by_that_parent_source_extent shared buf M F E B own
    fixed addr seed sizes boot p w live n
  have paid := (actual_mount_consumes_this_single_physical_filter M B p w j).2
  refine ⟨paid, Nat.max_le.mpr ⟨?_,ret⟩⟩
  have cut' : filterBits M B p w shared buf j≤recursiveResidentBits shared M B (.step p w) buf+delta :=
    cut.trans (Nat.add_le_add (unmounted_le_live shared buf M B p w) Ebound)
  have frames' : framePrefixBits M B p w shared buf n≤recursiveResidentBits shared M B (.step p w) buf+delta :=
    frames.trans (Nat.add_le_add_left Ebound _)
  have worst := Nat.max_le.mpr ⟨cut',frames'⟩
  have rooted := Nat.add_le_add_right (Nat.add_le_add_right worst
    (literalControlPath M F E B own (.step p w))) roster
  have budget : recursiveResidentBits shared M B (.step p w) buf+delta+
        literalControlPath M F E B own (.step p w)+roster≤H := by
    calc
      _ = recursiveResidentBits shared M B (.step p w) buf+
          literalControlPath M F E B own (.step p w)+roster+delta := by ac_rfl
      _ ≤ H := Nat.add_le_add base (Nat.le_max_left _ (4*width))
  exact rooted.trans budget

#print axioms return_cut_fits_existing_reserve_plus_two_pairs
#print axioms existing_live_path_bounds_mount_and_retirement_by_a_max
end
end J6R72SameRunLocalPeak
