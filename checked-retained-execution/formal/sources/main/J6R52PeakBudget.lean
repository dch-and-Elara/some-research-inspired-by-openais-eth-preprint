
import J6R52PeakTrace
import J6R52PeakModeAtlas
import J6R51PeakScoped
import J6R50PeakLiteralAtlas

/-! The actual demand-produced ancestor bank and the actual online
arithmetic fields are measured on one path. At a new publication,
already produced page words enter once and at most one observed
copied header snapshot is added, not the whole observation trace. -/
namespace J6R52Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R50Peak J6R51Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3750
set_option maxHeartbeats 22000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page
local notation "P" => (Plan sel)

def numericAtlasRoof (initial : L) (M0 p0 pageBound high : ℕ) : ℕ :=
  residentAtlasBits initial+(96*M0/29)*(page+pageBound)+
    pathLimit s C*arithmeticFrameCap s C ell f.natDegree (absolutePrecision s M0 p0) high

def actualOnlineRoof (initial : L) (M0 p0 pageBound high fixed addr seed : ℕ) : ℕ :=
  numericAtlasRoof (s:=s) (C:=C) initial M0 p0 pageBound high+
    descriptorBudget initial M0 (pathLimit s C) fixed addr (sourceBodyCap s C seed)

theorem same_online_arithmetic_and_atlas_at_path
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (pageBound high : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (p : Path sel r c) :
    ∃ b,OnlineTrace M retire initial p b ∧
      residentAtlasBits (stackBank (borns M) initial p)+b≤
        numericAtlasRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high := by
  obtain ⟨b,trace⟩ := every_actual_online_path_has_joint_trace M retire initial fits p
  exact ⟨b,trace,Nat.add_le_add
    (scoped_generated_literal_page_bits (borns M) initial pageBound
      (actual_online_births_have_physical_page_count M) pageFit p)
    (actual_online_ancestor_field_bound trace high hi)⟩

theorem actual_online_path_has_joint_selected_bound
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (pageBound high fixed addr seed : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (p : Path sel r c) :
    ∃ b,OnlineTrace M retire initial p b ∧
      residentAtlasBits (stackBank (borns M) initial p)+b+
        directoryBits (stackBank (borns M) initial p)≤
        actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed := by
  obtain ⟨b,trace,m⟩ := same_online_arithmetic_and_atlas_at_path M retire initial fits pageBound high pageFit hi p
  have cap := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr (sourceBodyCap s C seed)
    (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot) p
  exact ⟨b,trace,Nat.add_le_add m cap⟩

theorem actual_online_publication_peak_at_next_slot
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial)
    (fits : q≤uniformWidth s C) (pageBound high fixed addr seed U : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (rootFit : ∀ row∈initial.headers,row.bytes.length≤U)
    (p : Path sel r c) (w : (P).Slot c) :
    let live := stackBank (borns M) initial p
    let j := (borns M p w).job
    let V := max U (fixed+(3*r.edges/29)*(addr+sourceBodyCap s C seed))
    ∃ b,OnlineTrace M retire initial (.step p w) b ∧
      ∀ snap∈selectedInstallSnapshots j.entry live.headers,
        residentAtlasBits live+pendingPageBits j+b+directoryBits live+snap.length≤
          actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed+
            (2*key+3*V+1) := by
  let live := stackBank (borns M) initial p
  let j := (borns M p w).job
  let body := sourceBodyCap s C seed
  let V := max U (fixed+(3*r.edges/29)*(addr+body))
  have headFit : SourceHeaderFit (borns M) fixed addr body :=
    geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot
  obtain ⟨b,trace,h⟩ := same_online_arithmetic_and_atlas_at_path M retire initial fits pageBound high pageFit hi
    (.step p w)
  change residentAtlasBits (afterOne live j)+b≤_ at h
  rw [true_queued_pages_are_exact_increment] at h
  have dir := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr body headFit p
  have newFit : j.entry.result.bytes.length≤V :=
    (next_descriptor_fits_geometric_cap (borns M) fixed addr body headFit p w).trans (le_max_right _ _)
  have oldFit := live_headers_fit_same_geometric_cap (borns M) initial fixed addr body headFit U rootFit p
  have fresh : ∀ row∈live.headers,row.id≠j.entry.result.id :=
    (legal p w).2.2 j List.mem_cons_self
  exact ⟨b,trace,fun snap on=>Nat.add_le_add (Nat.add_le_add h dir)
    (actual_fresh_install_temporary_bits j.entry live.headers fresh oldFit newFit snap on)⟩

#print axioms same_online_arithmetic_and_atlas_at_path
#print axioms actual_online_path_has_joint_selected_bound
#print axioms actual_online_publication_peak_at_next_slot
end J6R52Peak
