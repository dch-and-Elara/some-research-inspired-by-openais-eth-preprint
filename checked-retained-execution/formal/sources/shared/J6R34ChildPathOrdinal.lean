import J6R34ChildPathPorts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19500000
set_option maxRecDepth 2500

/-! The child's edge serials are copied from the true selected raw
half-ports, in exactly that order. In particular this order is not
obtained by a free use of the logical finite equivalence. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R21Ancestor
open J6R15ModeCost J6R25PreparedSupply J6R27OriginalGate J6R31RootResidentTables
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6ActiveRun
open J6R32ChildResidentTransfer

def copyEdgeIds {w : ℕ} (rows : List (PortRow w)) : Meter (List (Word w)) :=
  A1R12.mapMeter (fun x=>copyFixed x.address) w rows

def selectedEdgeBook {w : ℕ} (group : Word 6) (raw : List (PortRow w)) :
    Meter (List (Word w)) :=
  let groupRows := selectPorts group raw
  let out := copyEdgeIds groupRows.result
  ⟨out.result,groupRows.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C w : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)

noncomputable def halfOrder : List (HalfAt T v) :=
  childLaneOrder (layout T v) (axis T v) v.groupAt D.order

theorem half_order_is_selected :
    D.physicalSelected v.groupAt=(halfOrder T v D).map Subtype.val := by
  unfold PhysicalPorts.physicalSelected halfOrder childLaneOrder
  let p := fun h : Port v.parent.host.Edge=>
    retainedGroup v.parent.host.network (atGroup (layout T v) (axis T v)) h=v.groupAt
  change (D.order.filter fun x=>decide (p x))=(scanSubtype p D.order).map Subtype.val
  generalize D.order = ord
  induction ord with
  | nil => rfl
  | cons h xs ih =>
    by_cases ht : p h
    · simp only [scanSubtype,List.filter_cons,List.filterMap_cons,dif_pos ht,decide_eq_true ht,
        if_true,List.map_cons] at *
      rw [ih]
    · simp only [scanSubtype,List.filter_cons,List.filterMap_cons,dif_neg ht,decide_eq_false ht,
        Bool.false_eq_true,if_false] at *
      exact ih

theorem half_order_complete :
    (halfOrder T v D).Nodup ∧ ∀ x,x∈halfOrder T v D :=
  child_lane_order_complete (layout T v) (axis T v) v.groupAt D.order D.nodup D.complete

theorem half_order_length : (halfOrder T v D).length=v.child.edges := by
  have hc := D.physical_count_is_child v.groupAt v.probeAt v.modeAt
  rw [half_order_is_selected T v D,List.length_map] at hc
  exact hc

noncomputable def actualEdgeOrder : Fin v.child.edges≃v.child.host.Edge :=
  ((finCongr (half_order_length T v D).symm).trans
    (rosterIndex (halfOrder T v D) (half_order_complete T v D).1 (half_order_complete T v D).2)).trans
    (childHalves T v).symm

noncomputable def childKey (E : v.child.host.Edge) : Word w :=
  (D.record (childHalves T v E).val).address
  -- The finite equivalence is a specification of the copied key.

theorem child_key_injective : Function.Injective (childKey T v D) :=
  D.distinct.comp (Subtype.val_injective.comp (childHalves T v).injective)

theorem get_half_by_actual_order :
    List.ofFn (fun j=>childHalves T v (actualEdgeOrder T v D j))=halfOrder T v D := by
  apply List.ext_getElem
  · rw [List.length_ofFn,half_order_length T v D]
  · intro j hj hj'
    rw [List.getElem_ofFn]
    simp only [actualEdgeOrder,Equiv.trans_apply,Equiv.apply_symm_apply]
    rfl

theorem exact_child_edge_book {port edgeW depth prec tc tz tm : ℕ}
    (J : NativeJob T v port edgeW depth prec tc tz tm) :
    let out := selectedEdgeBook J.gWord J.physical.raw
    let order := actualEdgeOrder T v J.physical
    out.result=List.ofFn (fun j=>childKey T v J.physical (order j)) ∧
      out.result.Nodup ∧
      out.steps≤7+(J.physical.raw.map rowScanFee).sum+v.child.edges*(4*port+5) := by
  let P := selectPorts J.gWord J.physical.raw
  have q : J.gWord=word v.groupAt.val :=
    (valued_word J.gWord).symm.trans (congrArg word J.gExact)
  have v1 : P.result=(halfOrder T v J.physical).map (fun u=>J.physical.record u.val) := by
    unfold P
    rw [q,J.physical.physical_port_select,half_order_is_selected T v J.physical,List.map_map]
    rfl
  let out := copyEdgeIds P.result
  obtain ⟨got,outFee⟩ := A1R12.mapMeter_exact
    (fun x : PortRow port=>copyFixed x.address) port (3*port+1)
    P.result (fun u _=>by change (copyFixed u.address).steps≤_; rw [copy_fixed_exact])
  have outVal : out.result=P.result.map PortRow.address :=
    got.trans (List.map_congr_left (fun u _=>congrArg Meter.result (copy_fixed_exact u.address)))
  rw [v1,List.map_map] at outVal
  have endVal : out.result=List.ofFn (fun j=>childKey T v J.physical (actualEdgeOrder T v J.physical j)) := by
    rw [outVal,←get_half_by_actual_order T v J.physical,List.map_ofFn]
    rfl
  have l : P.result.length=v.child.edges := by rw [v1,List.length_map,half_order_length T v J.physical]
  have cost1 : P.steps=3+(J.physical.raw.map rowScanFee).sum :=
    (select_ports_exact J.gWord J.physical.raw).2
  have cost2 : out.steps≤v.child.edges*(4*port+5) := by
    change out.steps≤P.result.length*((3*port+1)+port+4) at outFee
    rw [l] at outFee
    simpa only [show (3*port+1)+port+4=4*port+5 by omega] using outFee
  have inj : Function.Injective (fun j=>childKey T v J.physical (actualEdgeOrder T v J.physical j)) :=
    (child_key_injective T v J.physical).comp (actualEdgeOrder T v J.physical).injective
  refine ⟨endVal,?_,?_⟩
  · change out.result.Nodup
    rw [endVal]
    exact List.nodup_ofFn.mpr inj
  · change P.steps+out.steps+4≤_
    rw [cost1]
    omega

#print axioms half_order_is_selected
#print axioms half_order_complete
#print axioms half_order_length
#print axioms child_key_injective
#print axioms get_half_by_actual_order
#print axioms exact_child_edge_book
end J6R34ChildPath
