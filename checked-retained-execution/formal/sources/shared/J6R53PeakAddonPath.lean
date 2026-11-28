import J6R53PeakAddonCore
import J6R52PeakCachedStack

/-! Separate lifetime accounts for a site's mounted frame cache and its
indexed addon bank. The latter has two rows per edge of the PARENT
where the site was created, not two rows per child edge. Including
every installed bank on the current path is a conservative reserve;
no pointer reuse or simultaneous Lean heap residency is asserted. -/
namespace J6R53PeakAddon
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 17000000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)

def parentEdgesOnPath : {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step (c:=x) p _ => parentEdgesOnPath p+x.edges

theorem actual_parent_edge_sum_plus_endpoint (p : Path sel r c) :
    parentEdgesOnPath p+c.edges=(edgeStack p).sum := by
  induction p with
  | root => simp [edgeStack,parentEdgesOnPath]
  | step p w ih =>
    simp only [edgeStack,parentEdgesOnPath,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,ih]

theorem parent_edge_sum_uniform (p : Path sel r c) :
    parentEdgesOnPath p≤(32*r.edges/29)-c.edges := by
  have h := edgeStack_geometric p
  rw [←actual_parent_edge_sum_plus_endpoint p] at h
  omega

def sourceBankAt (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c) :
    Meter (ResidentBank (sourceState M p w)) :=
  installResidentBank (sourceState M p w)

def addonStackRows (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step p w => addonStackRows M p+(sourceBankAt M p w).result.rows.length

def addonStackBits (M : OnlineMachine T key prec tw bw page q) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _, .root => 0
  | _, .step p w => addonStackBits M p+(residentAddonPayload (sourceBankAt M p w).result).length

theorem exact_separate_bank_rows_on_same_path (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) :
    addonStackRows M p=2*parentEdgesOnPath p := by
  induction p with
  | root => simp [addonStackRows,parentEdgesOnPath]
  | @step x p w ih =>
    simp only [addonStackRows,parentEdgesOnPath,ih,Nat.mul_add]
    have h : (sourceBankAt M p w).result.rows.length=2*x.edges :=
      true_resident_bank_rows (sourceBankAt M p w).result
    exact congrArg (fun z=>2*parentEdgesOnPath p+z) h

/-- In particular the first paid sidecar cannot be tried with a
    child-sized row allocation. This is a live typed slot, not a
    synthetic chart with an unconstrained edge count. -/
theorem first_paid_index_has_more_than_twice_child_rows
    (M : OnlineMachine T key prec tw bw page q) (w : (P).Slot r) :
    let entrance : Path sel r r := .root
    2*((P).child r w).edges<(sourceBankAt M entrance w).result.rows.length := by
  let entrance : Path sel r r := .root
  have h : (sourceBankAt M entrance w).result.rows.length=2*r.edges :=
    true_resident_bank_rows (sourceBankAt M entrance w).result
  have m := child_edge_shrink w
  have pos : 0<r.edges := lt_of_le_of_lt (Nat.zero_le _) w.property
  change 2*((P).child r w).edges<(sourceBankAt M entrance w).result.rows.length
  rw [h]
  omega

def commonAddonRowCap (s addr owner key prec page : ℕ) : ℕ :=
  addr+addonCap owner (Nat.clog 2 s) key prec page

theorem exact_site_parent_rows_have_uniform_width
    (M : OnlineMachine T key prec tw bw page q) (fixed addr owner : ℕ)
    (sizes : EntryWidths M fixed addr) (owners : OwnerWidth M owner)
    (p : Path sel r c) (w : (P).Slot c) :
    (residentAddonPayload (sourceBankAt M p w).result).length≤
      (2*c.edges)*commonAddonRowCap s addr owner key prec page := by
  let X := sourceState M p w
  have h := (true_resident_bank_selected_fields (sourceBankAt M p w).result).2
  have add : X.birth.port≤addr := by
    have e := (sizes p w).2
    change X.birth.port+6≤addr at e
    omega
  have hOwn : X.site.ownerWidth≤owner := owners p w
  have hDim : dim (p.ticket w)≤Nat.clog 2 s := bits_le_lam _ _
  have k : X.birth.port+addonCap X.site.ownerWidth (dim (p.ticket w)) key prec page≤
      commonAddonRowCap s addr owner key prec page := by
    unfold commonAddonRowCap addonCap
    omega
  exact h.trans (Nat.mul_le_mul_left _ k)

theorem actual_path_indexed_addon_words_bounded
    (M : OnlineMachine T key prec tw bw page q) (fixed addr owner : ℕ)
    (sizes : EntryWidths M fixed addr) (owners : OwnerWidth M owner)
    (p : Path sel r c) :
    addonStackBits M p≤2*((32*r.edges/29)-c.edges)*commonAddonRowCap s addr owner key prec page := by
  let U := commonAddonRowCap s addr owner key prec page
  have h : addonStackBits M p≤(2*parentEdgesOnPath p)*U := by
    induction p with
    | root => simp [addonStackBits,parentEdgesOnPath]
    | step p w ih =>
      simp only [addonStackBits,parentEdgesOnPath,Nat.mul_add,Nat.add_mul]
      exact Nat.add_le_add ih (exact_site_parent_rows_have_uniform_width M fixed addr owner sizes owners p w)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (parent_edge_sum_uniform p)))

theorem actual_separate_addon_and_frame_fields_share_the_same_path
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed owner : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (owners : OwnerWidth M owner) (p : Path sel r c) :
    addonStackBits M p+cacheStackBits M p≤
      2*((32*r.edges/29)-c.edges)*commonAddonRowCap s addr owner key prec page+
        (3*r.edges/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) :=
  Nat.add_le_add (actual_path_indexed_addon_words_bounded M fixed addr owner sizes owners p)
    (actual_cached_path_frame_bytes M fixed addr seed owner sizes boot owners p)

#print axioms actual_parent_edge_sum_plus_endpoint
#print axioms parent_edge_sum_uniform
#print axioms first_paid_index_has_more_than_twice_child_rows
#print axioms exact_separate_bank_rows_on_same_path
#print axioms exact_site_parent_rows_have_uniform_width
#print axioms actual_path_indexed_addon_words_bounded
#print axioms actual_separate_addon_and_frame_fields_share_the_same_path
end
end J6R53PeakAddon
