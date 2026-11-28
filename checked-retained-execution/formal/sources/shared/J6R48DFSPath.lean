import J6R32StatefulArithmeticPath
import J6R16ModeCostPath

/-! Exact geometric budget of the real Appendix D slot stack.
A path tracks occurrences, not merely endpoint reachability. Its list
contains the root and every active/leaf call up to the current node. -/
namespace J6R48DFS
open scoped Polynomial
open J1PPrinted
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R32StatefulArithmetic

set_option autoImplicit false

variable {f : ℤ[X]} {ell s C : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}

/-- Youngest last, with repetitions left intact. -/
noncomputable def edgeStack : {par : Call (PhysicalHost f ell)} → Path sel r par → List ℕ
  | _, .root => [r.edges]
  | _, .step (c:=par) p w => edgeStack p ++ [((Plan sel).child par w).edges]

def moves : {par : Call (PhysicalHost f ell)} → Path sel r par → ℕ
  | _, .root => 0
  | _, .step p _ => moves p + 1

theorem child_edge_shrink {par : Call (PhysicalHost f ell)} (w : (Plan sel).Slot par) :
    32 * ((Plan sel).child par w).edges ≤ 3 * par.edges :=
  (Childs sel).bound par w.property w.val

theorem stack_exact_depth (p : Path sel r c) :
    c.depth = r.depth + moves p ∧ (edgeStack p).length = moves p + 1 := by
  induction p with
  | root => simp [moves,edgeStack]
  | @step par p w ih =>
    have next : ((Plan sel).child par w).depth=par.depth+1 := rfl
    simp only [moves,edgeStack,List.length_append,List.length_cons,List.length_nil]
    omega

/-- A telescoping bound keeps the source constants 32 and 3.
It includes the possibly edgeless current call; no artificial deletion
of isolated vertices or merger of parallel occurrences is used. -/
theorem edgeStack_potential (p : Path sel r c) :
    29 * (edgeStack p).sum + 3*c.edges ≤ 32*r.edges := by
  induction p with
  | root => simp only [edgeStack,List.sum_cons,List.sum_nil,add_zero]; omega
  | @step par p w ih =>
    have h := child_edge_shrink (sel:=sel) w
    simp only [edgeStack,List.sum_append,List.sum_cons,List.sum_nil,add_zero]
    omega

theorem edgeStack_geometric (p : Path sel r c) :
    29 * (edgeStack p).sum ≤ 32*r.edges :=
  (Nat.le_add_right _ _).trans (edgeStack_potential p)

theorem printed_stack_level_bound (cfg : RootBounds s C f) (hr : Stable s C r)
    (d₀ : r.depth=0) (p : Path sel r c) :
    (edgeStack p).length ≤ pathLimit s C+1 := by
  have h := (stack_exact_depth p)
  have b := path_depth_bound cfg sel p.reached hr d₀
  omega

#print axioms child_edge_shrink
#print axioms stack_exact_depth
#print axioms edgeStack_potential
#print axioms edgeStack_geometric
#print axioms printed_stack_level_bound
end J6R48DFS
