import J6R34ChildPathOrdinal

/-! One fixed literal (centre, probe, exponent occurrence) has exactly
64 native group arms. Each arm uses the corresponding genuine child
call; their union is the parent port roster, not a union of Pages. -/
namespace J6R36RouteConservation
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Repack J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
set_option autoImplicit false
set_option maxHeartbeats 22500000
set_option maxRecDepth 2700

variable {f : ℤ[X]} {ell s C w : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}

/-- Change only the actual group address field. All other fields,
including the parent and the active proof, come from the named call. -/
noncomputable def withGroup (v : Ticket sel r) (g : Fin 64) : Ticket sel r :=
  ⟨v.parent,v.path,⟨⟨v.centerAt,v.probeAt,v.modeAt,g⟩,v.slot.property⟩⟩

theorem with_original_group (v : Ticket sel r) : withGroup v v.groupAt=v := by
  cases v
  rfl

variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)

/-- The actual byte-roster indices of all arms, with each arm using its
own true size and the same parent tape's restricted order. -/
noncomputable def allGroupIndices :
    (Σ g : Fin 64,Fin (withGroup v g).child.edges) ≃ Port v.parent.host.Edge :=
  (Equiv.sigmaCongrRight (fun g : Fin 64=>
    (actualEdgeOrder T (withGroup v g) D).trans (childHalves T (withGroup v g)))).trans
    (allPortsEquiv v.parent.host.network (atGroup (layout T v) (axis T v)))

theorem all_group_indices_route (g : Fin 64) (i : Fin (withGroup v g).child.edges) :
    allGroupIndices T v D ⟨g,i⟩ =
      (childHalves T (withGroup v g) (actualEdgeOrder T (withGroup v g) D i)).val :=
  rfl

theorem port_has_its_one_named_arm (p : Port v.parent.host.Edge) :
    let pos := (allGroupIndices T v D).symm p
    pos.1=physicalGroup sel (ticketReady T v) v.centerAt p ∧
      (∀ q : Σ g : Fin 64,Fin (withGroup v g).child.edges,
        allGroupIndices T v D q=p → q=pos) := by
  let pos := (allGroupIndices T v D).symm p
  have H : allGroupIndices T v D pos=p :=
    (allGroupIndices T v D).apply_symm_apply p
  have hx : physicalGroup sel (ticketReady T v) v.centerAt
      (allGroupIndices T v D pos)=pos.1 := by
    exact (childHalves T (withGroup v pos.1)
      (actualEdgeOrder T (withGroup v pos.1) D pos.2)).property
  rw [H] at hx
  exact ⟨hx.symm,fun q h=>(allGroupIndices T v D).injective (h.trans H.symm)⟩

theorem all_named_children_conserve (D : PhysicalPorts sel (ticketReady T v) v.centerAt w) :
    (∑ g : Fin 64,(withGroup v g).child.edges)=2*v.parent.edges := by
  letI := v.parent.host.finiteEdge
  have cnt : Fintype.card v.parent.host.Edge=v.parent.edges := (ticketReady T v).edgeCount
  have c := Fintype.card_congr (allGroupIndices T v D)
  rw [Fintype.card_sigma,Fintype.card_sum,cnt,←two_mul] at c
  simpa only [Fintype.card_fin] using c

theorem same_tape_selected_for_each_named_child (g : Fin 64) :
    ((selectPorts (word g.val) D.raw).result).length=(withGroup v g).child.edges := by
  rw [D.physical_port_select g,List.length_map]
  exact D.physical_count_is_child g v.probeAt v.modeAt

theorem all_named_raw_scans_conserve :
    (∑ g : Fin 64,((selectPorts (word g.val) D.raw).result).length)=2*v.parent.edges := by
  have e := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 64))=Finset.univ)
    (fun g _=>same_tape_selected_for_each_named_child T v D g)
  exact e.trans (all_named_children_conserve T v D)

theorem real_parent_tape_has_two_records_per_edge : D.raw.length=2*v.parent.edges := by
  classical
  letI := v.parent.host.finiteEdge
  have cnt : Fintype.card v.parent.host.Edge=v.parent.edges := (ticketReady T v).edgeCount
  have univ : D.order.toFinset=(Finset.univ : Finset (Port v.parent.host.Edge)) := by
    ext p
    simp only [List.mem_toFinset,D.complete p,Finset.mem_univ]
  rw [D.source,List.length_map,←List.toFinset_card_of_nodup D.nodup,univ,
    Finset.card_univ,Fintype.card_sum,cnt,two_mul]

theorem record_occurs_just_in_its_group (p : Port v.parent.host.Edge) (g : Fin 64) :
    D.record p∈(selectPorts (word g.val) D.raw).result ↔
      physicalGroup sel (ticketReady T v) v.centerAt p=g := by
  rw [D.physical_port_select g,List.mem_map]
  constructor
  · rintro ⟨q,hq,eq⟩
    have eq' : q=p := D.distinct (congrArg PortRow.address eq)
    subst q
    exact decide_eq_true_eq.mp (List.mem_filter.mp hq).2
  · intro hg
    exact ⟨p,List.mem_filter.mpr ⟨D.complete p,decide_eq_true hg⟩,rfl⟩

theorem cross_group_physical_keys_injective :
    Function.Injective (fun i : Σ g : Fin 64,Fin (withGroup v g).child.edges =>
      (D.record (allGroupIndices T v D i)).address) :=
  D.distinct.comp (allGroupIndices T v D).injective

theorem named_child_declines (g : Fin 64) :
    (withGroup v g).child.depth=v.parent.depth+1 ∧
      32*(withGroup v g).child.edges≤3*v.parent.edges ∧
      (withGroup v g).child.edges≤v.parent.edges/8 ∧
      (withGroup v g).child.edges<v.parent.edges := by
  let u := withGroup v g
  have bound : 32*(withGroup v g).child.edges≤3*v.parent.edges :=
    (Childs sel).bound u.parent u.slot.property u.slot.val
  have hp : 0<v.parent.edges := Nat.zero_lt_of_lt v.slot.property
  refine ⟨rfl,bound,?_,?_⟩ <;> omega

end J6R36RouteConservation
#print axioms J6R36RouteConservation.with_original_group
#print axioms J6R36RouteConservation.all_group_indices_route
#print axioms J6R36RouteConservation.port_has_its_one_named_arm
#print axioms J6R36RouteConservation.all_named_children_conserve
#print axioms J6R36RouteConservation.same_tape_selected_for_each_named_child
#print axioms J6R36RouteConservation.all_named_raw_scans_conserve
#print axioms J6R36RouteConservation.real_parent_tape_has_two_records_per_edge
#print axioms J6R36RouteConservation.record_occurs_just_in_its_group
#print axioms J6R36RouteConservation.cross_group_physical_keys_injective
#print axioms J6R36RouteConservation.named_child_declines
