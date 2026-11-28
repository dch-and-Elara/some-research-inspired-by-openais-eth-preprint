import J6R75RawPeakFoldBound
import J6R68RecursivePeakBound
import J6R54PeakInputOccurrencePath

/-! The source directory and wire-frame payload are bounded independently
of the raw arithmetic. Adding the actual named raw ancestor reserve
does not count its stock or earlier centre words a second time. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4400
set_option maxHeartbeats 5300000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def physicalCarrierRoof (shared : ℕ) (initial : L)
    (r : Call (PhysicalHost f ell)) (pageBound fixed addr seed owner s C : ℕ) : ℕ :=
  shared+(residentAtlasBits initial+(96*r.edges/29)*(page+pageBound))+
    descriptorBudget initial r.edges (pathLimit s C) fixed addr (sourceBodyCap s C seed)+
    (bankFrameBits initial+pathLimit s C*frameSlope (prec:=prec) (s:=s) (r:=r))+
    cachedIngressRoof r.edges s C addr seed owner key prec page

theorem named_physical_path_carrier_fits_without_any_arithmetic
    (M : Machine) (initial : L) (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner) (p : Path sel r c) :
    recursiveResidentBits shared M initial p 0≤
      physicalCarrierRoof shared initial r pageBound fixed addr seed owner s C := by
  let B := stackBank (borns M) initial p
  have atlas := scoped_generated_literal_page_bits (borns M) initial pageBound
    (actual_online_births_have_physical_page_count M) pageFit p
  have dirs := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr (sourceBodyCap s C seed)
    (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot) p
  have frame := actual_live_frame_stack_is_bounded M initial p
  have h0 := measured_fields_of_both_source_records_and_caches M fixed addr seed owner sizes boot owners p
  have contraction := Nat.mul_le_mul_left 2 (Nat.sub_le (32*r.edges/29) c.edges)
  have ingress : cachedIngressBits M p≤cachedIngressRoof r.edges s C addr seed owner key prec page :=
    h0.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ contraction) _)
  have core :
      recursiveResidentBits shared M initial p 0=
        shared+residentAtlasBits B+directoryBits B+bankFrameBits B+cachedIngressBits M p := by
    simp only [recursiveResidentBits,mountedSelectedBits,Nat.add_zero,B]
    ac_rfl
  rw [core]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left atlas shared) dirs) frame) ingress

def rawCarrierRoof (shared : ℕ) (initial : L)
    (r : Call (PhysicalHost f ell)) (pageBound fixed addr seed owner s C q : ℕ) : ℕ :=
  let low := absolutePrecision s r.edges r.prec
  physicalCarrierRoof shared initial r pageBound fixed addr seed owner s C+
    pathLimit s C*selectedRawLayerRoof s C q ell f.natDegree low (absoluteHighCap s C low)

theorem raw_ancestor_and_same_physical_carrier_fit_together
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (shared pageBound fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr)
    (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (p : Path sel r c) (bits : ℕ) (stack : ActualRawAncestorStack M F chart E B own tails p bits) :
    recursiveResidentBits shared M B p bits≤rawCarrierRoof shared B r pageBound fixed addr seed owner s C q := by
  have physical := named_physical_path_carrier_fits_without_any_arithmetic M B shared
    pageBound fixed addr seed owner pageFit sizes boot owners p
  have counted := actual_raw_ancestor_stack_selected_words_fit_one_reserve_per_move M F chart E B own tails
    p bits stack
  have real :
      recursiveResidentBits shared M B p bits=recursiveResidentBits shared M B p 0+bits := by
    simp only [recursiveResidentBits,Nat.add_zero]
    ac_rfl
  rw [real]
  exact Nat.add_le_add physical counted

#print axioms named_physical_path_carrier_fits_without_any_arithmetic
#print axioms raw_ancestor_and_same_physical_carrier_fit_together
end
end J6R75RawPeak
