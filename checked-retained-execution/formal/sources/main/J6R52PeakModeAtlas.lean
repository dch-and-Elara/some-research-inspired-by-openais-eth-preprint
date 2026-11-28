import J6R52PeakModePath
import J6R51PeakOnlineDirectory
import J6R50PeakLiteralAtlas

/-! The mode/cursor words and actual physical descriptors occupying
one successful online path, as distinct from all local scratch. -/
namespace J6R52Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R50Peak J6R51Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3750
set_option maxHeartbeats 18500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page
local notation "P" => (Plan sel)

def ExactPageFit (M : OnlineMachine T key prec tw bw page q) (pageBound : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    let e := (borns M p w).job.immutable.payload.payload
    ∀ y∈e.pages,(originPayload y.payload).length≤pageBound

theorem actual_online_births_have_physical_page_count (M : OnlineMachine T key prec tw bw page q) :
    AllExactPages (borns M) := by
  intro c p w
  exact actual_compiled_occurrence_census (sourceState M p w).input

def onlineModeDirectoryRoof (initial : L) (M0 p0 pageBound fixed addr seed : ℕ) (s C : ℕ) : ℕ :=
  let P0 := absolutePrecision s M0 p0
  residentAtlasBits initial+(96*M0/29)*(page+pageBound)+
    pathLimit s C*(absoluteModeCap s C ell f.natDegree P0+weightCap s C P0)+
    descriptorBudget initial M0 (pathLimit s C) fixed addr (sourceBodyCap s C seed)

theorem actual_online_path_mode_and_directory_bound
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (pageBound fixed addr seed : ℕ)
    (pageFit : ExactPageFit M pageBound) (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (p : Path sel r c) :
    ∃ b,OnlineModePath M retire initial p b ∧
      residentAtlasBits (stackBank (borns M) initial p)+b+
        directoryBits (stackBank (borns M) initial p)≤
        onlineModeDirectoryRoof initial r.edges r.prec pageBound fixed addr seed s C := by
  obtain ⟨b,trace⟩ := every_actual_online_path_tracks_modes M retire initial fits p
  have atlas := scoped_generated_literal_page_bits (borns M) initial pageBound
    (actual_online_births_have_physical_page_count M) pageFit p
  have dir := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr (sourceBodyCap s C seed)
    (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot) p
  exact ⟨b,trace,Nat.add_le_add (Nat.add_le_add atlas (actual_online_path_tracks_mode_bit_bound trace)) dir⟩

#print axioms actual_online_births_have_physical_page_count
#print axioms actual_online_path_mode_and_directory_bound
end J6R52Peak
