import J6R57LiveSpaceCachedMode
import J6R57LiveSpaceCachedNumeric
import J6R52PeakBudget
import J6R54PeakInputOccurrencePath

/-! A single typed path of the actual cached interpreter witnesses
all of the retained selected fields together. This is conservative
encoded space, not a claim that runtime objects cannot alias. -/
namespace J6R57LiveSpace
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49LiveBits J6R50Peak J6R51Peak J6R51Online J6R52Peak J6R52CacheWhole
open J6R53PeakAddon J6R54PeakInput

set_option autoImplicit false
set_option maxRecDepth 3950
set_option maxHeartbeats 27000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

inductive CachedPausePath (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : CachedPausePath M retire initial (.root : Path sel r r) 0
  | step {x : Call (PhysicalHost f ell)} {p : Path sel r x} {bits : ℕ}
      (prior : CachedPausePath M retire initial p bits) (w : (P).Slot x)
      (o : NativeSuspension (C:=C) (sel:=sel) x)
      (mode : SawCachedMode M retire initial p w o)
      (num : OnlineNumeric M p w) (visit : PaidBankVisit M retire initial p w) :
      CachedPausePath M retire initial (.step p w)
        (bits+(o.measure.bits+(storedModeWeights o).length+(cachedNumericPayload num retire initial).length))

theorem every_actual_cached_occurrence_has_its_joint_pause
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial) (fits : q≤uniformWidth s C) (p : Path sel r c) :
    ∃ bits,CachedPausePath M retire initial p bits := by
  induction p with
  | root => exact ⟨0,.root⟩
  | step p w ih =>
    obtain ⟨bits,got⟩ := ih
    obtain ⟨o,seen⟩ := each_cached_slot_has_its_real_mode_event M retire initial fits p w
    obtain ⟨num⟩ := each_online_slot_has_the_native_numeric_pause M p w
    exact ⟨_,.step got w o seen num (every_legal_paid_occurrence_uses_its_physical_bank M retire initial legal p w).1⟩

theorem actual_cached_arithmetic_stack_cap
    {M : OnlineMachine T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {b : ℕ} (trace : CachedPausePath M retire initial p b)
    (high : ℕ) (fit : ActualHighFit M high) :
    b≤pathLimit s C*arithmeticFrameCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) high := by
  let A := arithmeticFrameCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) high
  have counted : b≤moves p*A := by
    induction trace with
    | root => simp [moves]
    | @step x old used prior w o mode num visit ih =>
      have d := mode_selected_payload_absolute T old o
      have v := actual_site_weight_bits T old o
      have n := actual_cache_numeric_payload_bound num retire initial high fit
      have h : o.measure.bits+(storedModeWeights o).length+(cachedNumericPayload num retire initial).length≤A :=
        Nat.add_le_add (Nat.add_le_add d v) n
      simp only [moves,Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add ih h
  exact counted.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))

def cachedIngressBits (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) : ℕ :=
  physicalInputStackBits M p+(rawStackBits M p+addonStackBits M p+cacheStackBits M p)

def cachedIngressRoof (M0 s C addr seed owner key prec page : ℕ) : ℕ :=
  2*(32*M0/29)*(addr+sourceBodyCap s C seed+rawAndIndexedRowCap s addr owner key prec page)+
    (3*M0/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed)

def selectedCachedStackBits (shared : ℕ) (M : OnlineMachine T key prec tw bw page q)
    (initial : L) (p : Path sel r c) (arithmetic : ℕ) : ℕ :=
  shared+(residentAtlasBits (stackBank (borns M) initial p)+arithmetic+
    directoryBits (stackBank (borns M) initial p))+cachedIngressBits M p

theorem all_named_fields_on_same_cached_path_have_joint_cap
    (shared : ℕ) (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (pageBound high fixed addr seed owner : ℕ)
    (pageFit : ExactPageFit M pageBound) (hi : ActualHighFit M high)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed) (owners : OwnerWidth M owner)
    (legal : ReadyOnStack (borns M) initial) (p : Path sel r c) :
    ∃ bits,CachedPausePath M retire initial p bits ∧
      selectedCachedStackBits shared M initial p bits≤
        shared+actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed+
          cachedIngressRoof r.edges s C addr seed owner key prec page := by
  obtain ⟨bits,observed⟩ := every_actual_cached_occurrence_has_its_joint_pause M retire initial legal fits p
  have atlas := scoped_generated_literal_page_bits (borns M) initial pageBound
    (actual_online_births_have_physical_page_count M) pageFit p
  have kernel := actual_cached_arithmetic_stack_cap observed high hi
  have rows := bounded_descriptor_stack_at_original_start (borns M) initial fixed addr (sourceBodyCap s C seed)
    (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes boot) p
  have central : residentAtlasBits (stackBank (borns M) initial p)+bits+
      directoryBits (stackBank (borns M) initial p)≤
        actualOnlineRoof (s:=s) (C:=C) initial r.edges r.prec pageBound high fixed addr seed :=
    Nat.add_le_add (Nat.add_le_add atlas kernel) rows
  have cap := measured_fields_of_both_source_records_and_caches M fixed addr seed owner sizes boot owners p
  have contraction := Nat.mul_le_mul_left 2 (Nat.sub_le (32*r.edges/29) c.edges)
  have width : cachedIngressBits M p≤cachedIngressRoof r.edges s C addr seed owner key prec page :=
    cap.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ contraction) _)
  exact ⟨bits,observed,Nat.add_le_add (Nat.add_le_add_left central shared) width⟩

#print axioms every_actual_cached_occurrence_has_its_joint_pause
#print axioms actual_cached_arithmetic_stack_cap
#print axioms all_named_fields_on_same_cached_path_have_joint_cap
end
end J6R57LiveSpace
