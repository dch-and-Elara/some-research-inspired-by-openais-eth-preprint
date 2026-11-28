import J6R58LeafScalePrecision
import J6R57LeafCapClock
import J6R57LeafCapStored
import J6R21LeafBudgetBind

/-! Uniform finite-field arithmetic part of the actual leaf prefactor.
The per-entry reading bill is kept separately, so a padded or unpriced
resident chart cannot be hidden in the arithmetic estimate. -/
namespace J6R58LeafScale
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R10Repack J6R24MeteredRecursion J6R26DescriptorTree J6R25PreparedSupply J6R16ModeCost
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34ChildPath J6R48DFS
open J6R50SourceProducer J6R51Leaf J6R57LeafCap J6R48Leaf J6R49Leaf J6R21Leaf J6R50Peak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3700

theorem actual_raw_leaf_scale_arithmetic_separate {e ell p m v E L P H V bill : ℕ} (hp : 0<p)
    (he : e≤E) (hl : ell≤L) (hr : p≤P) (hm : m≤H) (hv : v≤V) :
    rawLeafScale e ell p m v bill hp≤bill+leafArithmeticScale E L P H V 0 := by
  have h := call_leaf_fee_uniform_dims hp he hl hr (le_refl (0:ℕ)) hv (le_refl (0:ℕ))
  simp [callLeafFee,polynomialLeafFee,reverseFee] at h
  have hm' := Nat.mul_le_mul_left 3 hm
  unfold rawLeafScale reverseFee leafArithmeticScale
  simp only [Nat.zero_add]
  omega

noncomputable section
variable {f : ℤ[X]} {ell s C key page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem true_ordered_leaf_keeps_all_vertices (edgeEq : c.host.edgeCount=c.edges)
    (cmd : c.host.Row⊕c.host.Col→PageReadCode c.edges key page) :
    (PagedLeaf.toRaw (orderedCommands edgeEq cmd)).rows.length=vertexCount c.host := by
  change ((vertexList c.host).map (fun v=>(v,cmd v))).length=_
  rw [List.length_map]
  exact complete_vertex_list_length c.host _ (vertexList_nodup _) (vertexList_complete _)

include T in
theorem actual_leaf_field_width_and_vertices (path : Path sel r c) :
    let F := T.frame path.reached
    F.words.length=4*Nat.clog 2 s ∧
      c.prec≤r.prec+160*C*s^2 ∧
      vertexCount c.host≤vertexCount r.host+4*(C*s) := by
  have hs : 1<s := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1
    (show 0<Nat.clog 2 s from (by decide : (0:ℕ)<1024).trans_le (root_lambda_large cfg))
  have edges := actual_source_path_edges_le (cfg:=cfg) sel T.rootStable (.root : Path sel r r)
  have p := (absolute_inherited_precision_cap cfg sel T.rootStable path).trans
    (absolute_precision_from_printed_source s C r.edges r.prec hs edges)
  have vertices := (native_vertex_cap cfg sel path.reached T.rootStable).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left 4 edges) _)
  exact ⟨(Frame.natDegree hf (T.frame path.reached)).trans cfg.coefficient,p,vertices⟩

#print axioms actual_raw_leaf_scale_arithmetic_separate
#print axioms true_ordered_leaf_keeps_all_vertices
#print axioms actual_leaf_field_width_and_vertices
end
end J6R58LeafScale
