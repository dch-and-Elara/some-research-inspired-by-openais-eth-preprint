import J6R36RouteConservationPorts

/-! Neither the two ends of a parent edge nor two parallel edge
occurrences are merged in the actual ordered, copied byte keys. At equal
physical packet seat owners, parallel occurrences may also be parallel
in the child; the distinct edge identities remain. -/
namespace J6R36RouteConservation
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 2600

variable {f : ℤ[X]} {ell s C w : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable (D : PhysicalPorts sel (ticketReady T v) v.centerAt w)

noncomputable def slotOfPort (p : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt) : Fin v.child.edges :=
  (indexedHalf T v D).symm ⟨p,hp⟩

@[simp] theorem indexed_half_at_port (p : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt) :
    (indexedHalf T v D (slotOfPort T v D p hp)).val=p :=
  congrArg Subtype.val ((indexedHalf T v D).apply_symm_apply ⟨p,hp⟩)

theorem semantic_endpoints_at_port (p : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt) :
    let ed := actualEdgeOrder T v D (slotOfPort T v D p hp)
    childVertices T v (.inl (v.child.host.network.row ed))=
      .inl (⟨owner v.parent.host.network p,hp⟩ : OldAt T v) ∧
    childVertices T v (.inr (v.child.host.network.col ed))=
      .inr (atPacket (layout T v) (edge p)) := by
  let ed := actualEdgeOrder T v D (slotOfPort T v D p hp)
  have H := actual_child_half_endpoints T v ed
  have e : (childHalves T v ed).val=p := indexed_half_at_port T v D p hp
  refine ⟨H.1.trans (congrArg Sum.inl ?_),H.2.trans ?_⟩
  · exact Subtype.ext (congrArg (owner v.parent.host.network) e)
  · exact congrArg (fun a=>Sum.inr (atPacket (layout T v) (edge a))) e

theorem parallel_endpoints_in_child (p q : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt)
    (hq : physicalGroup sel (ticketReady T v) v.centerAt q=v.groupAt)
    (ownerEq : owner v.parent.host.network p=owner v.parent.host.network q)
    (packetEq : atPacket (layout T v) (edge p)=atPacket (layout T v) (edge q)) :
    let i := actualEdgeOrder T v D (slotOfPort T v D p hp)
    let j := actualEdgeOrder T v D (slotOfPort T v D q hq)
    v.child.host.network.row i=v.child.host.network.row j ∧
    v.child.host.network.col i=v.child.host.network.col j := by
  have e := semantic_endpoints_at_port T v D p hp
  have e' := semantic_endpoints_at_port T v D q hq
  refine ⟨?_,?_⟩
  · exact Sum.inl.inj ((childVertices T v).injective
      (e.1.trans ((congrArg Sum.inl (Subtype.ext ownerEq)).trans e'.1.symm)))
  · exact Sum.inr.inj ((childVertices T v).injective
      (e.2.trans ((congrArg Sum.inr packetEq).trans e'.2.symm)))

variable {port edgeW depth prec tc tz tm : ℕ}
variable (J : NativeJob T v port edgeW depth prec tc tz tm)

theorem copied_port_at (p : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt) :
    let i := slotOfPort T v J.physical p hp
    let book := selectedEdgeBook J.gWord J.physical.raw
    book.result[i.val]?=some (J.physical.record p).address := by
  exact (native_book_address_at T v J (slotOfPort T v J.physical p hp)).trans
    (congrArg (fun u=>some (J.physical.record u).address) (indexed_half_at_port T v J.physical p hp))

theorem distinct_parent_ports_in_native_book (p q : Port v.parent.host.Edge)
    (hp : physicalGroup sel (ticketReady T v) v.centerAt p=v.groupAt)
    (hq : physicalGroup sel (ticketReady T v) v.centerAt q=v.groupAt)
    (different : p≠q) :
    let i := slotOfPort T v J.physical p hp
    let j := slotOfPort T v J.physical q hq
    let book := selectedEdgeBook J.gWord J.physical.raw
    i≠j ∧ book.result[i.val]?≠book.result[j.val]? := by
  refine ⟨?_,?_⟩
  · intro eq
    apply different
    exact (indexed_half_at_port T v J.physical p hp).symm.trans
      ((congrArg (fun k=>(indexedHalf T v J.physical k).val) eq).trans
        (indexed_half_at_port T v J.physical q hq))
  · intro eq
    apply different
    exact J.physical.distinct (Option.some.inj
      ((copied_port_at T v J p hp).symm.trans (eq.trans (copied_port_at T v J q hq))))

theorem both_ends_in_same_group_are_not_merged (e : v.parent.host.Edge)
    (hr : physicalGroup sel (ticketReady T v) v.centerAt (.inl e)=v.groupAt)
    (hc : physicalGroup sel (ticketReady T v) v.centerAt (.inr e)=v.groupAt) :
    let i := slotOfPort T v J.physical (.inl e) hr
    let j := slotOfPort T v J.physical (.inr e) hc
    let book := selectedEdgeBook J.gWord J.physical.raw
    indexedIdentity T v J.physical i=(e,false) ∧
      indexedIdentity T v J.physical j=(e,true) ∧
      i≠j ∧ book.result[i.val]?≠book.result[j.val]? := by
  refine ⟨?_,?_,distinct_parent_ports_in_native_book T v J (.inl e) (.inr e) hr hc (by intro h; cases h)⟩
  · exact congrArg (portIdentity _) (indexed_half_at_port T v J.physical (.inl e) hr)
  · exact congrArg (portIdentity _) (indexed_half_at_port T v J.physical (.inr e) hc)

/-- If equal-endpoint parent occurrences also have the same packet,
the same-side children actually share both endpoints, yet their emitted
keys and their explicit original occurrence identities differ. -/
theorem parent_parallel_edges_survive_same_packet
    (e e' : v.parent.host.Edge) (separate : e≠e') (b : Bool)
    (sameRow : v.parent.host.network.row e=v.parent.host.network.row e')
    (sameCol : v.parent.host.network.col e=v.parent.host.network.col e')
    (samePacket : atPacket (layout T v) e=atPacket (layout T v) e')
    (selected : physicalGroup sel (ticketReady T v) v.centerAt ((portIdentity _).symm (e,b))=v.groupAt) :
    ∃ i j : Fin v.child.edges,
      indexedIdentity T v J.physical i=(e,b) ∧ indexedIdentity T v J.physical j=(e',b) ∧
      i≠j ∧
      (selectedEdgeBook J.gWord J.physical.raw).result[i.val]? ≠
        (selectedEdgeBook J.gWord J.physical.raw).result[j.val]? ∧
      v.child.host.network.row (actualEdgeOrder T v J.physical i)=
        v.child.host.network.row (actualEdgeOrder T v J.physical j) ∧
      v.child.host.network.col (actualEdgeOrder T v J.physical i)=
        v.child.host.network.col (actualEdgeOrder T v J.physical j) := by
  let p := (portIdentity _).symm (e,b)
  let q := (portIdentity _).symm (e',b)
  have own : owner v.parent.host.network p=owner v.parent.host.network q := by
    cases b
    · exact congrArg Sum.inl sameRow
    · exact congrArg Sum.inr sameCol
  have qSel : physicalGroup sel (ticketReady T v) v.centerAt q=v.groupAt := by
    change atGroup (layout T v) (axis T v) (owner v.parent.host.network q)=v.groupAt
    rw [←own]
    exact selected
  have pe : edge p=e := congrArg Prod.fst ((portIdentity _).apply_symm_apply (e,b))
  have qe : edge q=e' := congrArg Prod.fst ((portIdentity _).apply_symm_apply (e',b))
  have pq : p≠q := fun h=>separate (pe.symm.trans ((congrArg edge h).trans qe))
  have pg : atPacket (layout T v) (edge p)=atPacket (layout T v) (edge q) := by
    rw [pe,qe,samePacket]
  let i := slotOfPort T v J.physical p selected
  let j := slotOfPort T v J.physical q qSel
  have distinct := distinct_parent_ports_in_native_book T v J p q selected qSel pq
  have ends := parallel_endpoints_in_child T v J.physical p q selected qSel own pg
  refine ⟨i,j,?_,?_,distinct.1,distinct.2,ends.1,ends.2⟩
  · exact (congrArg (portIdentity _) (indexed_half_at_port T v J.physical p selected)).trans
      ((portIdentity _).apply_symm_apply (e,b))
  · exact (congrArg (portIdentity _) (indexed_half_at_port T v J.physical q qSel)).trans
      ((portIdentity _).apply_symm_apply (e',b))

end J6R36RouteConservation
#print axioms J6R36RouteConservation.indexed_half_at_port
#print axioms J6R36RouteConservation.semantic_endpoints_at_port
#print axioms J6R36RouteConservation.parallel_endpoints_in_child
#print axioms J6R36RouteConservation.copied_port_at
#print axioms J6R36RouteConservation.distinct_parent_ports_in_native_book
#print axioms J6R36RouteConservation.both_ends_in_same_group_are_not_merged
#print axioms J6R36RouteConservation.parent_parallel_edges_survive_same_packet
