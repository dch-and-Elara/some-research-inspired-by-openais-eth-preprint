import J6R58LeafScalePrecision
import J6R57LeafCapStored

/-! Price the real stored edge-book scan from its complete physical half
port tape. The only size premises are the chosen actual address width
and an actual encoded body length bound. -/
namespace J6R58LeafScale
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R10Repack J6R24MeteredRecursion J6R26DescriptorTree J6R25PreparedSupply J6R16ModeCost
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34ChildPath J6R48DFS
open J6R50SourceProducer J6R51Leaf J6R57LeafCap
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4300
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem every_literal_parent_half_port_is_in_the_book
    (par : Path sel r c) (w : (Plan sel).Slot c)
    (site : StoredSite T (par.ticket w) key prec tw bw page) :
    site.birth.native.physical.raw.length=2*c.edges := by
  classical
  let H := site.birth.native.physical
  letI := c.host.finiteEdge
  have n := H.nodup.getEquivOfForallMemList H.order H.complete
  have count : H.order.length=Nat.card (J6R10Repack.Port c.host.Edge) :=
    (Nat.card_fin _).symm.trans (Nat.card_congr n)
  have edgeCount : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact (ticketReady T (par.ticket w)).edgeCount
  rw [show site.birth.native.physical.raw=H.order.map H.record from H.source,List.length_map,count]
  unfold J6R10Repack.Port
  rw [Nat.card_sum,edgeCount]
  omega

theorem exact_edge_book_shape_fee_from_source_size
    (par : Path sel r c) (w : (Plan sel).Slot c)
    (site : StoredSite T (par.ticket w) key prec tw bw page) {K U : ℕ}
    (width : site.birth.port≤K)
    (bodies : ∀ row∈site.birth.native.physical.raw,row.body.length≤U) :
    bookShapeFee site≤7+2*(C*s)*(2*K+3*U+81)+(C*s)*(4*K+5) := by
  let H := site.birth.native.physical
  have parent := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable par
  have child := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable (Path.step par w)
  have hs : (H.raw.map rowScanFee).sum≤H.raw.length*(2*K+3*U+81) :=
    list_sum_cap _ _ _ (by
      intro b hb
      have h := bodies b hb
      unfold rowScanFee
      omega)
  have n : H.raw.length=2*c.edges := every_literal_parent_half_port_is_in_the_book par w site
  rw [n] at hs
  have cost : (H.raw.map rowScanFee).sum≤2*(C*s)*(2*K+3*U+81) :=
    hs.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 parent))
  have wd : 4*site.birth.port+5≤4*K+5 := by omega
  have ep : (par.ticket w).child.edges≤C*s := child
  unfold bookShapeFee
  exact Nat.add_le_add (Nat.add_le_add_left cost _) (Nat.mul_le_mul ep wd)

#print axioms every_literal_parent_half_port_is_in_the_book
#print axioms exact_edge_book_shape_fee_from_source_size
end
end J6R58LeafScale
