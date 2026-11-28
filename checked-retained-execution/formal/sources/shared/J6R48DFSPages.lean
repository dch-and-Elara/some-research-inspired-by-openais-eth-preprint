import J6R48DFSPath

/-! The weight of a newly installed Appendix D occurrence is the number
of physical packet columns, including empty columns. Its length comes
from the same dependent child call whose edges shrink, not from a raw
directory-size hypothesis. No conversion from page count to bit width
is implicit. -/
namespace J6R48DFS
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J6R32StatefulArithmetic J1PPrinted P11FullPacking

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 2500

variable {f : ℤ[X]} {ell s C : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

/-- These are the actual child column names. Every padded packet remains
a column, even when there is no emitted half-port in the chosen group. -/
noncomputable def newPages {par : Call (PhysicalHost f ell)} (w : (Plan sel).Slot par) : ℕ :=
  Nat.card ((Plan sel).child par w).host.Col

noncomputable def pagesOnStack : {par : Call (PhysicalHost f ell)} → Path sel r par → ℕ
  | _, .root => 0
  | _, .step p w => pagesOnStack p + newPages (sel:=sel) w

theorem packet_columns_are_pages (d : Ready S (sourceDelta s) c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t →₀ ℕ) (g : Fin 64) :
    (packetOfSite sel d t z β g).Col =
      Page ((S).levelBits c.depth) (packing sel d).copies (Fin 64) := rfl

theorem actual_padded_packet_width (cfg : RootBounds s C f) (hr : Stable s C r)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    newPages (sel:=sel) w * 2^((S).levelBits c.depth) ≤ 3*c.edges := by
  let d := ready_reachable cfg sel p.reached hr w.property
  let t := w.val.1
  let z := w.val.2.1
  let β := siteTuple sel d w.val
  let g := w.val.2.2.2
  have H := congrArg (fun x : Call (PhysicalHost f ell) => x.host.Col)
    (child_exact sel d w.val)
  have E : ((Plan sel).child c w).host.Col =
      Page ((S).levelBits c.depth) (packing sel d).copies (Fin 64) :=
    H.trans (packet_columns_are_pages d t z β g)
  rw [newPages,E]
  letI := c.host.finiteEdge
  have cap := physical_packet_count (packing sel d)
  have hcard : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact d.edgeCount
  exact hcard ▸ cap

theorem actual_packet_columns_le (cfg : RootBounds s C f) (hr : Stable s C r)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    newPages (sel:=sel) w ≤ 3*c.edges :=
  (Nat.le_mul_of_pos_right _ (by positivity)).trans (actual_padded_packet_width cfg hr p w)

/-- The cost of newly created page columns is charged against the
**parent's** edge count, not the possibly zero child edge count. -/
theorem pagesOnStack_parent_budget (cfg : RootBounds s C f) (hr : Stable s C r) (p : Path sel r c) :
    pagesOnStack p + 3*c.edges ≤ 3*(edgeStack p).sum := by
  induction p with
  | root => simp [pagesOnStack,edgeStack]
  | step p w ih =>
    have hk := actual_packet_columns_le cfg hr p w
    simp only [pagesOnStack,edgeStack,List.sum_append,List.sum_cons,List.sum_nil,add_zero]
    omega

/-- True live generated page-count peak; the root/original file,
transient compiler scratch, cursor state, and interpolation words are
separate. The bound holds at every reached occurrence, not just a
maximal-depth leaf and not just for a distinct-graph quotient. -/
theorem printed_packet_peak (cfg : RootBounds s C f) (hr : Stable s C r) (p : Path sel r c) :
    29*pagesOnStack p + 96*c.edges ≤ 96*r.edges := by
  have hp := Nat.mul_le_mul_left 29 (pagesOnStack_parent_budget cfg hr p)
  have he := Nat.mul_le_mul_left 3 (edgeStack_potential p)
  omega

theorem generated_packets_linear (cfg : RootBounds s C f) (hr : Stable s C r) (p : Path sel r c) :
    pagesOnStack p ≤ (96*r.edges)/29 :=
  (Nat.le_div_iff_mul_le (by decide)).mpr (by
    have h := printed_packet_peak cfg hr p
    omega)

#print axioms packet_columns_are_pages
#print axioms actual_padded_packet_width
#print axioms actual_packet_columns_le
#print axioms pagesOnStack_parent_budget
#print axioms printed_packet_peak
#print axioms generated_packets_linear
end J6R48DFS
