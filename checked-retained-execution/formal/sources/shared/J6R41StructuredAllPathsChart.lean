import J6R34ChildPathChart

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000

/-! Physical half-occurrence and side are invariant under the already
proved actual child chart transport. These equivalences appear only
in the correctness proof, not as uncharged byte-address conversions. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R34ChildPath J6R26DescriptorTree
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

def castPort {f : ℤ[X]} {ell : ℕ} {a b : Point f ell} (e : a=b) :
    PortAt a→PortAt b :=
  cast (congrArg PortAt e)

theorem cast_port_preserves_side {f : ℤ[X]} {ell : ℕ} {a b : Point f ell} (e : a=b)
    (x : PortAt a) : side (castPort e x).val=side x.val := by
  subst b
  rfl

theorem cast_port_edge {f : ℤ[X]} {ell : ℕ} {a b : Point f ell} (e : a=b)
    (x : PortAt a) :
    edge (castPort e x).val=cast (congrArg (fun z : Point f ell=>z.host.Edge) e) (edge x.val) := by
  subst b
  rfl

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

theorem selected_retained_chart (u : v.child.host.Row⊕v.child.host.Col) (old : OldAt T v)
    (h : childVertices T v u=.inl old) : point v.child.host u=(retainedMove T v old).next := by
  have H := actual_child_vertex_chart T v u
  rw [h] at H
  exact H.trans (actual_retained_point T v old).symm

theorem selected_packet_chart (u : v.child.host.Row⊕v.child.host.Col) (k : PageAt T v)
    (h : childVertices T v u=.inr k) : point v.child.host u=bornPoint T v k := by
  have H := actual_child_vertex_chart T v u
  rw [h] at H
  exact H

theorem retained_chart_uses_given_half (u : v.child.host.Row⊕v.child.host.Col) (old : OldAt T v)
    (e : point v.child.host u=(retainedMove T v old).next)
    (x : PortAt (point v.child.host u)) :
    edge (castPort e x).val=childHalves T v (edge x.val) ∧ side x.val=false := by
  refine ⟨(cast_port_edge e x).trans rfl,?_⟩
  exact (cast_port_preserves_side e x).symm.trans ((retainedMove T v old).side_left _)

theorem fresh_chart_uses_given_half (u : v.child.host.Row⊕v.child.host.Col) (k : PageAt T v)
    (e : point v.child.host u=bornPoint T v k)
    (x : PortAt (point v.child.host u)) :
    edge (castPort e x).val=childHalves T v (edge x.val) ∧ side x.val=true := by
  refine ⟨(cast_port_edge e x).trans rfl,?_⟩
  exact (cast_port_preserves_side e x).symm.trans (actual_fresh_port T v k _).1

#print axioms cast_port_preserves_side
#print axioms cast_port_edge
#print axioms selected_retained_chart
#print axioms selected_packet_chart
#print axioms retained_chart_uses_given_half
#print axioms fresh_chart_uses_given_half
end J6R41StructuredAllPaths