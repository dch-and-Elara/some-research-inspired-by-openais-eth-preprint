import J6R54PeakInputCore
import J6R53PeakAddonVisits

/-! The true raw field and separately installed index are both observed
on the same logical cache-aware path. The bound is a reserve even if
the implementation has already released some field. The newest raw
emitter output and the stored input are never two separate raw lists
in this observer. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 18000000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "J" => PageJob f ell key prec tw bw page
local notation "L" => PageBank f ell key prec tw bw page

def rawStackBits (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step p w => rawStackBits M p+(storedRawBits (sourceState M p w)).length

def addonAddressStack (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step (c:=par) p w => addonAddressStack M p+(2*par.edges)*(sourceState M p w).birth.port

theorem exact_path_indexed_words_split_into_raw_and_address_fields
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) :
    addonStackBits M p=rawStackBits M p+addonAddressStack M p := by
  induction p with
  | root => simp [addonStackBits,rawStackBits,addonAddressStack]
  | step p w ih =>
    have h := actual_sidecar_extra_bits_are_its_address_lane (sourceBankAt M p w).result
    change (residentAddonPayload (sourceBankAt M p w).result).length=
      (storedRawBits (sourceState M p w)).length+_ at h
    simp only [addonStackBits,rawStackBits,addonAddressStack,ih,h]
    ac_rfl

def rawAndIndexedRowCap (s addr owner key prec page : ℕ) : ℕ :=
  addr+2*addonCap owner (Nat.clog 2 s) key prec page

theorem true_site_tapes_counted_together_at_one_entry
    (M : OnlineMachine T key prec tw bw page q) (fixed addr owner : ℕ)
    (sizes : EntryWidths M fixed addr) (ownerFits : OwnerWidth M owner)
    (p : Path sel r c) (w : (P).Slot c) :
    let X := sourceState M p w
    let into := (sourceBankAt M p w).result
    (storedRawBits X).length+(residentAddonPayload into).length≤
      (2*c.edges)*rawAndIndexedRowCap s addr owner key prec page := by
  let X := sourceState M p w
  let into := (sourceBankAt M p w).result
  have localBill := true_sidecar_install_fields_bound X.site
  rw [the_two_distinct_tapes_have_exact_pair_payload into] at localBill
  have ha : X.birth.port≤addr := by
    have h := (sizes p w).2
    change X.birth.port+6≤addr at h
    omega
  have ho : X.site.ownerWidth≤owner := ownerFits p w
  have hd : dim (p.ticket w)≤Nat.clog 2 s := bits_le_lam _ _
  have cap : X.birth.port+2*addonCap X.site.ownerWidth (dim (p.ticket w)) key prec page≤
      rawAndIndexedRowCap s addr owner key prec page := by
    unfold rawAndIndexedRowCap addonCap
    omega
  exact localBill.trans (Nat.mul_le_mul_left _ cap)

theorem true_path_raw_and_indexed_reserve
    (M : OnlineMachine T key prec tw bw page q) (fixed addr owner : ℕ)
    (sizes : EntryWidths M fixed addr) (owners : OwnerWidth M owner) (p : Path sel r c) :
    rawStackBits M p+addonStackBits M p≤
      2*((32*r.edges/29)-c.edges)*rawAndIndexedRowCap s addr owner key prec page := by
  let U := rawAndIndexedRowCap s addr owner key prec page
  have localTotal : rawStackBits M p+addonStackBits M p≤(2*parentEdgesOnPath p)*U := by
    induction p with
    | root => simp [rawStackBits,addonStackBits,parentEdgesOnPath]
    | @step par p w ih =>
      have h := true_site_tapes_counted_together_at_one_entry M fixed addr owner sizes owners p w
      change (storedRawBits (sourceState M p w)).length+
        (residentAddonPayload (sourceBankAt M p w).result).length≤(2*par.edges)*U at h
      simp only [rawStackBits,addonStackBits,parentEdgesOnPath,Nat.mul_add,Nat.add_mul]
      omega
  exact localTotal.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (parent_edge_sum_uniform p)))

theorem actual_raw_indexed_and_frame_reserves_same_stack
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed owner : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (owners : OwnerWidth M owner) (p : Path sel r c) :
    rawStackBits M p+addonStackBits M p+cacheStackBits M p≤
      2*((32*r.edges/29)-c.edges)*rawAndIndexedRowCap s addr owner key prec page+
        (3*r.edges/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) :=
  Nat.add_le_add (true_path_raw_and_indexed_reserve M fixed addr owner sizes owners p)
    (actual_cached_path_frame_bytes M fixed addr seed owner sizes boot owners p)

inductive ObservedRawPath (M : OnlineMachine T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) : {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | start : ObservedRawPath M retire initial (.root : Path sel r r) 0
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x} {used : ℕ}
      (previous : ObservedRawPath M retire initial p used) (w : (P).Slot x)
      (observed : PaidBankVisit M retire initial p w) :
      ObservedRawPath M retire initial (.step p w)
        (used+(storedRawBits (sourceState M p w)).length)

theorem actual_cache_aware_entries_carry_the_observed_raw_field
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (legal : ReadyOnStack (borns M) initial) (p : Path sel r c) :
    ObservedRawPath M retire initial p (rawStackBits M p) := by
  induction p with
  | root => exact .start
  | step p w ih =>
    exact .enter ih w (every_legal_paid_occurrence_uses_its_physical_bank M retire initial legal p w).1

#print axioms exact_path_indexed_words_split_into_raw_and_address_fields
#print axioms true_site_tapes_counted_together_at_one_entry
#print axioms true_path_raw_and_indexed_reserve
#print axioms actual_raw_indexed_and_frame_reserves_same_stack
#print axioms actual_cache_aware_entries_carry_the_observed_raw_field
end
end J6R54PeakInput
