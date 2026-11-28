import J6R48DFSPages
import J6R48DFSScope
import J6R32ChildResidentTransferMask

/-! Count the actual visible atlas records, not a free capacity field
from a descriptor. A genuine all-page birth has one row per physical
column. The per-site equality uses its written atlas order, and the
whole scoped bank counts badges by nested occurrence, never by the
union of the graphs or atlas values. -/
namespace J6R48DFS
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R32ChildResidentTransfer J6R21Ancestor P11FullPacking

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 2100

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem ordered_child_page_count (a copies : ℕ) :
    (orderedChildPages a copies).length=Nat.card (Page a copies (Fin 64)) := by
  classical
  let v := orderedChildPages a copies
  have nd : v.Nodup := (child_pages_complete a copies).1
  have full : v.toFinset=(Finset.univ : Finset (Page a copies (Fin 64))) := by
    ext k
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact (child_pages_complete a copies).2.1 k
  rw [Nat.card_eq_fintype_card,←Finset.card_univ,←full,List.toFinset_card_of_nodup nd]

theorem physical_order_counts_actual_birth (cfg : RootBounds s C f) (hr : Stable s C r)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    let d := ready_reachable cfg sel p.reached hr w.property
    (orderedChildPages ((S).levelBits c.depth) (packing sel d).copies).length =
      newPages (sel:=sel) w := by
  let d := ready_reachable cfg sel p.reached hr w.property
  let t := w.val.1
  let z := w.val.2.1
  let β := siteTuple sel d w.val
  let g := w.val.2.2.2
  have a := congrArg (fun v : Call (PhysicalHost f ell)=>v.host.Col) (child_exact sel d w.val)
  have E : ((Plan sel).child c w).host.Col =
      Page ((S).levelBits c.depth) (packing sel d).copies (Fin 64) :=
    a.trans (packet_columns_are_pages d t z β g)
  dsimp only
  rw [newPages,E,ordered_child_page_count]

def bankPageCount (B : L) : ℕ :=
  (B.records.map (fun rec=>rec.payload.payload.pages.length)).sum

/-- Just enough of a birth receipt to translate visible records into
the physical column count. The real R33 issuer provides it from its
certified ordered-page atlas, not a guessed bound on arbitrary lists. -/
def AllExactPages (born : Births T key prec tw bw page) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    (born p w).job.immutable.payload.payload.pages.length=newPages (sel:=sel) w

theorem exact_stack_atlas_rows (born : Births T key prec tw bw page) (initial : L)
    (hRows : AllExactPages born) (p : Path sel r c) :
    bankPageCount (stackBank born initial p)=bankPageCount initial+pagesOnStack p := by
  induction p with
  | root => simp only [stackBank,pagesOnStack,Nat.add_zero]
  | step p w ih =>
    change (born p w).job.immutable.payload.payload.pages.length+
      bankPageCount (stackBank born initial p) = bankPageCount initial+(pagesOnStack p+newPages (sel:=sel) w)
    rw [hRows p w,ih]
    ac_rfl

theorem actual_stack_atlas_peak (born : Births T key prec tw bw page) (initial : L)
    (hRows : AllExactPages born) (p : Path sel r c) :
    bankPageCount (stackBank born initial p) ≤ bankPageCount initial+(96*r.edges)/29 := by
  rw [exact_stack_atlas_rows born initial hRows p]
  exact Nat.add_le_add_left (generated_packets_linear cfg T.rootStable p) _

theorem bounded_visible_lookup (born : Births T key prec tw bw page) (initial : L)
    (addr : J6R15ModeCost.Word key) (p : Path sel r c) (d₀ : r.depth=0) :
    (locate addr (stackBank born initial p).records).steps ≤
      locateFee key (initial.records.length+J6R16ModeCost.pathLimit s C) := by
  apply (locate_bound addr _).trans
  unfold locateFee
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (visible_occurrence_limit born initial p d₀)) _

#print axioms ordered_child_page_count
#print axioms physical_order_counts_actual_birth
#print axioms exact_stack_atlas_rows
#print axioms actual_stack_atlas_peak
#print axioms bounded_visible_lookup
end J6R48DFS
