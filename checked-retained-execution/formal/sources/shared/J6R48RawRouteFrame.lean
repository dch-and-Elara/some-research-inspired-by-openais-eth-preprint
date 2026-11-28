import J6R48RawRouteWriter
import J6R41StructuredAllPathsSite
import J6R34ChildPathOrdinal

/-! Direct adjacent elaboration from the previous genuine descriptor,
without an oracle for the next physical row's ancestry bytes. The new
resident seat rows are in the literal selected child edge order. -/
namespace J6R48RawRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

def pairedPorts {E : Type} (xs : List E) : List (Port E) :=
  xs.flatMap (fun e=>[.inl e,.inr e])

theorem mem_paired_ports {E : Type} (p : Port E) (xs : List E) :
    p∈pairedPorts xs ↔ edge p∈xs := by
  cases p <;> simp [pairedPorts,List.mem_flatMap,edge]

theorem paired_ports_nodup {E : Type} (xs : List E) (h : xs.Nodup) :
    (pairedPorts xs).Nodup := by
  induction xs with
  | nil => simp [pairedPorts]
  | cons e xs ih =>
    obtain ⟨out,nd⟩ := List.nodup_cons.mp h
    change (([Sum.inl e,Sum.inr e] : List (Port E))++pairedPorts xs).Nodup
    simp only [List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,Sum.inl_ne_inr,
      false_or,mem_paired_ports,edge,Sum.elim_inl,Sum.elim_inr]
    exact ⟨out,out,ih nd⟩

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "E" => v.child.host.Edge
local notation "ord" => (actualEdgeOrder T v Q.native.physical)

def childOrder (_S : SiteInputs Q previous) : List E := List.ofFn (fun j=>ord j)

theorem child_order_complete :
    (childOrder S).Nodup ∧ ∀ e,e∈childOrder S := by
  constructor
  · exact List.nodup_ofFn.mpr (ord).injective
  · intro e
    exact List.mem_ofFn.mpr ⟨(ord).symm e,(ord).apply_symm_apply e⟩

noncomputable def frameOf (e : E) : FramedEdge Q.port S.ownerWidth key prec page :=
  S.frame (childHalves T v e)

theorem source_framed_in_child_order :
    S.write.result.framed=some ((childOrder S).map (frameOf S)) := by
  rw [(true_site_issuance S).2.2.2]
  congr 1
  rw [←get_half_by_actual_order T v Q.native.physical,List.map_ofFn,childOrder,List.map_ofFn]
  rfl

theorem frame_left_child_address (e : E) :
    (frameOf S e).left.id.edge=childKey T v Q.native.physical e := rfl

theorem frame_right_child_address (e : E) :
    (frameOf S e).right.id.edge=childKey T v Q.native.physical e := rfl


#print axioms mem_paired_ports
#print axioms paired_ports_nodup
#print axioms child_order_complete
#print axioms source_framed_in_child_order
#print axioms frame_left_child_address
#print axioms frame_right_child_address
end
end J6R48RawRoute

